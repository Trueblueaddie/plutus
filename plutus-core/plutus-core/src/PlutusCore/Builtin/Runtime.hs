{-# LANGUAGE LambdaCase #-}

{-# LANGUAGE StrictData #-}

module PlutusCore.Builtin.Runtime where

import PlutusPrelude

import PlutusCore.Builtin.KnownType
import PlutusCore.Evaluation.Machine.ExBudget

import Control.DeepSeq
import NoThunks.Class

-- | A 'BuiltinRuntime' represents a possibly partial builtin application.
-- We get an initial 'BuiltinRuntime' representing an empty builtin application (i.e. just the
-- builtin with no arguments) by instantiating (via 'fromBuiltinRuntimeOptions') a
-- 'BuiltinRuntimeOptions'.
--
-- Applying or type-instantiating a builtin peels off the corresponding constructor from its
-- 'BuiltinRuntime'.
--
-- 'BuiltinResult' contains the cost (an 'ExBudget') and the result (a @MakeKnownM val@) of the
-- builtin application. The cost is stored strictly, since the evaluator is going to look at it
-- and the result is stored lazily, since it's not supposed to be forced before accounting for the
-- cost of the application. If the cost exceeds the available budget, the evaluator discards the
-- the result of the builtin application without ever forcing it and terminates with evaluation
-- failure. Allowing the user to compute something that they don't have the budget for would be a
-- major bug.
--
-- Evaluators that ignore the entire concept of costing (e.g. the CK machine) may of course force
-- the result of the builtin application unconditionally.
data BuiltinRuntime val
    = BuiltinResult ExBudget ~(MakeKnownM val)
    -- 'ReadKnownM' is required here only for immediate unlifting, because deferred unlifting
    -- doesn't need the ability to fail in the middle of a builtin application, but having a uniform
    -- interface for both the ways of doing unlifting is way too convenient, hence we decided to pay
    -- the price (about 1-2% of total evaluation time) for now.
    | BuiltinExpectArgument (val -> ReadKnownM (BuiltinRuntime val))
    | BuiltinExpectForce (BuiltinRuntime val)

instance NoThunks (BuiltinRuntime val) where
    wNoThunks ctx = \case
        -- Unreachable, because we don't allow nullary builtins and the 'BuiltinArrow' case only
        -- checks for WHNF without recursing. Hence we can throw if we reach this clause somehow.
        BuiltinResult _ _          -> pure . Just $ ThunkInfo ctx
        -- This one doesn't do much. It only checks that the function stored in the 'BuiltinArrow'
        -- is in WHNF. The function may contain thunks inside of it. Not sure if it's possible to do
        -- better, since the final 'BuiltinResult' contains a thunk for the result of the builtin
        -- application anyway.
        BuiltinExpectArgument f    -> noThunks ctx f
        BuiltinExpectForce runtime -> noThunks ctx runtime

    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinRuntime"

-- | Determines how to unlift arguments. The difference is that with 'UnliftingImmediate' unlifting
-- is performed immediately after a builtin gets the argument and so can fail immediately too, while
-- with deferred unlifting all arguments are unlifted upon full saturation, hence no failure can
-- occur until that. The former makes it much harder to specify the behaviour of builtins and
-- so 'UnliftingDeferred' is the preferred mode.
data UnliftingMode
    = UnliftingImmediate
    | UnliftingDeferred

-- | A 'BuiltinRuntimeOptions' is a precursor to 'BuiltinRuntime'. One gets the latter from the
-- former by applying a function returning the runtime denotation of the builtin (either
-- '_broImmediateF' for immediate unlifting or '_broDeferredF' for deferred unlifting, see
-- 'UnliftingMode' for details) to a cost model.
data BuiltinRuntimeOptions val cost = BuiltinRuntimeOptions
    { _broImmediateF :: cost -> BuiltinRuntime val
    , _broDeferredF  :: cost -> BuiltinRuntime val
    }

-- | Convert a 'BuiltinRuntimeOptions' to a 'BuiltinRuntime' given an 'UnliftingMode' and a cost
-- model.
fromBuiltinRuntimeOptions
    :: UnliftingMode -> cost -> BuiltinRuntimeOptions val cost -> BuiltinRuntime val
fromBuiltinRuntimeOptions unlMode cost (BuiltinRuntimeOptions immF defF) =
    case unlMode of
        UnliftingImmediate -> immF cost
        UnliftingDeferred  -> defF cost
{-# INLINE fromBuiltinRuntimeOptions #-}

instance NFData (BuiltinRuntime val) where
    -- 'BuiltinRuntime' is strict (verified by the 'NoThunks' tests), hence we only need to force
    -- this to WHNF to get it forced to NF.
    rnf = rwhnf

-- | A 'BuiltinRuntime' for each builtin from a set of builtins. Just an 'Array' of cached
-- 'BuiltinRuntime's. We could instantiate 'BuiltinMeaning' on the fly and avoid caching
-- 'BuiltinRuntime' in an array, but we've tried it and it was much slower as we do rely on caching
-- (especially for costing).
newtype BuiltinsRuntime fun val = BuiltinsRuntime
    { unBuiltinRuntime :: fun -> BuiltinRuntime val
    }

instance (Bounded fun, Enum fun) => NFData (BuiltinsRuntime fun val) where
    rnf (BuiltinsRuntime env) = foldr (\fun res -> env fun `seq` res) () enumerate

instance NoThunks (BuiltinsRuntime fun val) where
    wNoThunks ctx (BuiltinsRuntime env) = noThunks ctx env
    showTypeOf = const "PlutusCore.Builtin.Runtime.BuiltinsRuntime"

-- | Look up the runtime info of a built-in function during evaluation.
lookupBuiltin :: fun -> BuiltinsRuntime fun val -> BuiltinRuntime val
-- @Data.Array@ doesn't seem to have a safe version of @(!)@, hence we use a prism.
lookupBuiltin fun (BuiltinsRuntime env) = env fun
{-# INLINE lookupBuiltin #-}
