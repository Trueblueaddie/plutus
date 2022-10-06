-- editorconfig-checker-disable-file
-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE StrictData        #-}
module PlutusLedgerApi.Internal.Eval
    (
      -- * Evaluation runtime system
      EvaluationContext

      -- * Evaluation of Scripts
    , evaluateScriptRestricting
    , evaluateScriptCounting
    , VerboseMode (..)

    -- * Evaluation result
    , LogOutput
    , EvaluationError (..)

      -- * Helpers
    , CostModelApplyError (..)
    , CostModelApplyWarn (..)
    , mkDynEvaluationContext
    ) where

import PlutusCore as ScriptPlutus (Version, defaultVersion)
import PlutusCore.Data as Plutus
import PlutusCore.Evaluation.Machine.ExBudget as Plutus
import PlutusCore.MkPlc qualified as UPLC
import PlutusCore.Pretty
import PlutusLedgerApi.Common.SerialisedScript
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC
import PlutusLedgerApi.Internal.SerialisedScript

import Control.Monad.Writer
import Data.Text as Text
import Data.Tuple
import Prettyprinter
import Control.Lens



import PlutusLedgerApi.Common.Versions

import PlutusCore
import PlutusCore.Evaluation.Machine.MachineParameters.Default
import PlutusCore.Evaluation.Machine.MachineParameters.DeferredMachineParameters
import PlutusCore.Evaluation.Machine.MachineParameters.ImmediateMachineParameters
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus

import PlutusPrelude
import NoThunks.Class
import Control.Monad.Except

-- | Errors that can be thrown when evaluating a Plutus script.
data EvaluationError =
    CekError (UPLC.CekEvaluationException NamedDeBruijn DefaultUni DefaultFun) -- ^ An error from the evaluator itself
    | DeBruijnError FreeVariableError -- ^ An error in the pre-evaluation step of converting from de-Bruijn indices
    | CodecError ScriptDecodeError -- ^ A deserialisation error
    | IncompatibleVersionError (ScriptPlutus.Version ()) -- ^ An error indicating a version tag that we don't support
    -- TODO: make this error more informative when we have more information about what went wrong
    | CostModelParameterMismatch -- ^ An error indicating that the cost model parameters didn't match what we expected
    deriving stock (Show, Eq)
makeClassyPrisms ''EvaluationError

instance AsScriptDecodeError EvaluationError where
    _ScriptDecodeError = _CodecError

instance Pretty EvaluationError where
    pretty (CekError e)      = prettyClassicDef e
    pretty (DeBruijnError e) = pretty e
    pretty (CodecError e) = viaShow e
    pretty (IncompatibleVersionError actual) = "This version of the Plutus Core interface does not support the version indicated by the AST:" <+> pretty actual
    pretty CostModelParameterMismatch = "Cost model parameters were not as we expected"

-- | The type of log output: just a list of 'Text'.
--
type LogOutput = [Text.Text]

-- | A simple toggle indicating whether or not we should produce logs.
data VerboseMode = Verbose | Quiet
    deriving stock (Eq)

{-|
Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
evaluateScriptRestricting
    :: PlutusVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> ExBudget        -- ^ The resource budget which must not be exceeded during evaluation
    -> SerialisedScript          -- ^ The script to evaluate
    -> [Plutus.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptRestricting lv pv verbose ectx budget p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.RestrictingSt (ExRestrictingBudget final), logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                (UPLC.restricting $ ExRestrictingBudget budget)
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure (budget `minusExBudget` final)

{-|
Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget.

Note: Parameterized over the ledger-plutus-version since the builtins allowed (during decoding) differs.
-}
evaluateScriptCounting
    :: PlutusVersion
    -> ProtocolVersion
    -> VerboseMode     -- ^ Whether to produce log output
    -> EvaluationContext -- ^ The cost model that should already be synced to the most recent cost-model-params coming from the current protocol
    -> SerialisedScript          -- ^ The script to evaluate
    -> [Plutus.Data]          -- ^ The arguments to the script
    -> (LogOutput, Either EvaluationError ExBudget)
evaluateScriptCounting lv pv verbose ectx p args = swap $ runWriter @LogOutput $ runExceptT $ do
    appliedTerm <- mkTermToEvaluate lv pv p args

    let (res, UPLC.CountingSt final, logs) =
            UPLC.runCekDeBruijn
                (toMachineParameters pv ectx)
                UPLC.counting
                (if verbose == Verbose then UPLC.logEmitter else UPLC.noEmitter)
                appliedTerm

    tell logs
    liftEither $ first CekError $ void res
    pure final

-- | Shared helper for the evaluation functions, deserialises the 'SerialisedScript' , applies it to its arguments, puts fakenamedebruijns, and scope-checks it.
mkTermToEvaluate
    :: (MonadError EvaluationError m)
    => PlutusVersion
    -> ProtocolVersion
    -> SerialisedScript
    -> [Plutus.Data]
    -> m (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())
mkTermToEvaluate lv pv bs args = do
    -- It decodes the program through the optimized ScriptForExecution. See `ScriptForExecution`.
    ScriptForExecution (UPLC.Program _ v t) <- deserialiseScriptForExecution lv pv bs
    unless (v == ScriptPlutus.defaultVersion ()) $ throwError $ IncompatibleVersionError v
    let termArgs = fmap (UPLC.mkConstant ()) args
        appliedT = UPLC.mkIterApp () t termArgs

    -- make sure that term is closed, i.e. well-scoped
    through (liftEither . first DeBruijnError . UPLC.checkScope) appliedT

{-| An opaque type that contains all the static parameters that the evaluator needs to evaluate a
script.  This is so that they can be computed once and cached, rather than recomputed on every
evaluation.

There are two sets of parameters: one is with immediate unlifting and the other one is with
deferred unlifting. We have to keep both of them, because depending on the language version
 either one has to be used or the other. We also compile them separately due to all the inlining
 and optimization that need to happen for things to be efficient.
-}
data EvaluationContext = EvaluationContext
    { machineParametersImmediate :: DefaultMachineParameters
    , machineParametersDeferred  :: DefaultMachineParameters
    }
    deriving stock Generic
    deriving anyclass (NFData, NoThunks)

{-|  Build the 'EvaluationContext'.

The input is a `Map` of `Text`s to cost integer values (aka `Plutus.CostModelParams`, `Alonzo.CostModel`)
See Note [Inlining meanings of builtins].
-}
mkDynEvaluationContext :: MonadError CostModelApplyError m => BuiltinVersion DefaultFun -> Plutus.CostModelParams -> m EvaluationContext
mkDynEvaluationContext ver newCMP =
    EvaluationContext
        <$> immediateMachineParameters ver newCMP
        <*> deferredMachineParameters ver newCMP

toMachineParameters :: ProtocolVersion -> EvaluationContext -> DefaultMachineParameters
toMachineParameters pv = case unliftingModeIn pv of
    UnliftingImmediate -> machineParametersImmediate
    UnliftingDeferred  -> machineParametersDeferred

-- | Which unlifting mode should we use in the given 'ProtocolVersion'
-- so as to correctly construct the machine's parameters
unliftingModeIn :: ProtocolVersion -> UnliftingMode
unliftingModeIn pv =
    -- This just changes once in vasil hf version 7.0
    if pv >= VasilPV then UnliftingDeferred else UnliftingImmediate

