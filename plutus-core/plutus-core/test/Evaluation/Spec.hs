{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Evaluation.Spec where

import Control.Monad.Except
import Data.ByteString qualified as BS
import Data.Functor ((<&>))
import Data.Int (Int64)
import Data.List.Extra qualified as List
import Data.Text (Text)
import Data.Type.Equality
import Data.Typeable (splitTyConApp)
import Evaluation.Machines (test_machines)
import Hedgehog hiding (Opaque, Var, eval)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusCore hiding (Term)
import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Data (Data (..))
import PlutusCore.Generators
import Prettyprinter
import Test.Tasty
import Test.Tasty.Hedgehog
import Type.Reflection
import Unsafe.Coerce

type Term = PLC.Term TyName Name DefaultUni DefaultFun ()

test_builtinsDon'tThrow :: TestTree
test_builtinsDon'tThrow =
  testGroup
    "Builtins don't throw"
    . fmap (\fun -> testProperty (show fun) $ prop_builtinsDon'tThrow fun)
    $ List.enumerate
      -- TODO: remove this
      List.\\ [ VerifySignature,
                VerifyEcdsaSecp256k1Signature,
                VerifySchnorrSecp256k1Signature
              ]

prop_builtinsDon'tThrow :: DefaultFun -> Property
prop_builtinsDon'tThrow bn = property $ do
  (args, argStrings) <- unzip <$> forAllNoShow (genArgs bn)
  let (res, logs) = runEmitter . runExceptT $ eval args argStrings
  case res of
    Right _ -> success
    Left err -> do
      liftIO $ do
        putStrLn "Builtin function evaluation failed"
        putStrLn $ "Function: " <> show bn
        putStrLn $ "Arguments: " <> show argStrings
        putStrLn $
          "Error: "
            <> ( case err of
                   KnownTypeEvaluationFailure -> "KnownTypeEvaluationFailure"
                   KnownTypeUnliftingError e ->
                     "KnownTypeUnliftingError: "
                       <> show (pretty e)
               )
        putStrLn $ "Execution log: " <> show logs
      failure
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning bn

    eval :: [Term] -> [String] -> MakeKnownM Term
    eval args0 argStrings = case meaning of
      BuiltinMeaning _ _ runtime -> go (_broRuntimeScheme runtime) (_broImmediateF runtime) args0
      where
        go ::
          forall n.
          RuntimeScheme n ->
          ToRuntimeDenotationType Term n ->
          [Term] ->
          MakeKnownM Term
        go sch f args = case (sch, args) of
          (RuntimeSchemeArrow sch', a : as) -> do
            res <- liftEither (f a)
            go sch' res as
          (RuntimeSchemeResult, []) -> f
          (RuntimeSchemeAll sch', _) -> go sch' f args
          _ -> error $ "Wrong number of args for builtin " <> show bn <> ": " <> show argStrings

-- | Generate arguments to a builtin function
genArgs :: DefaultFun -> Gen [(Term, String)]
genArgs bn = case bn of
  -- These functions are partial, so we manually generate their arguments.
  IndexByteString -> do
    s <- Gen.utf8 (Range.linear 5 100) Gen.enumBounded
    i :: Integer <- fromIntegral <$> Gen.int (Range.linear 0 (BS.length s - 1))
    pure [mkArg s, mkArg i]
  HeadList -> pure . pure . mkArg =<< Gen.list (Range.linear 1 100) genInteger
  TailList -> genArgs HeadList
  UnConstrData -> pure . pure . mkArg =<< genConstr 5
  UnMapData -> pure . pure . mkArg =<< genMap 5
  UnListData -> pure . pure . mkArg =<< genList 5
  UnIData -> pure . pure . mkArg =<< genI
  UnBData -> pure . pure . mkArg =<< genB
  -- The rest are total functions and we generate the arguments based on their `TypeScheme`s.
  _ -> sequenceA $ case meaning of
    BuiltinMeaning tySch _ _ -> go tySch
      where
        go :: forall args res. TypeScheme Term args res -> [Gen (Term, String)]
        go = \case
          TypeSchemeResult    -> []
          TypeSchemeArrow sch -> genArg (typeRep @(Head args)) : go sch
          TypeSchemeAll _ sch -> go sch
  where
    meaning :: BuiltinMeaning Term (CostingPart DefaultUni DefaultFun)
    meaning = toBuiltinMeaning bn

-- | Generate one argument to a builtin function based on its `TypeRep`.
genArg :: forall k (a :: k). TypeRep a -> Gen (Term, String)
genArg tr
  | Just HRefl <- eqTypeRep tr (typeRep @()) = pure $ mkArg ()
  | Just HRefl <- eqTypeRep tr (typeRep @Integer) = pure . mkArg =<< genInteger
  | Just HRefl <- eqTypeRep tr (typeRep @Int) = pure . mkArg =<< genInteger
  | Just HRefl <- eqTypeRep tr (typeRep @Bool) = pure . mkArg =<< Gen.bool
  | Just HRefl <- eqTypeRep tr (typeRep @BS.ByteString) = pure . mkArg =<< genByteString
  | Just HRefl <- eqTypeRep tr (typeRep @Text) = pure . mkArg =<< genText
  | Just HRefl <- eqTypeRep tr (typeRep @Data) = pure . mkArg =<< genData 5
  | Just [SomeTypeRep tr1, SomeTypeRep tr2] <- matchTyCon @(,) tr = do
      (arg1, argStr1) <- genArg tr1
      (arg2, argStr2) <- genArg tr2
      case (arg1, arg2) of
        (Constant _ (Some (ValueOf uni1 val1)), Constant _ (Some (ValueOf uni2 val2))) ->
          pure
            ( Constant
                ()
                ( someValueOf
                    (DefaultUniApply (DefaultUniApply DefaultUniProtoPair uni1) uni2)
                    (val1, val2)
                ),
              show (argStr1, argStr2)
            )
        _ -> error "genArg: encountered non-Constant term"
  | Just [SomeTypeRep trElem] <- matchTyCon @[] tr = do
      (arg, _) <- genArg trElem
      case arg of
        Constant _ (Some (ValueOf uniElem (_ :: b))) -> do
          (args, argStrings) <- unzip <$> (Gen.list (Range.linear 0 10) $ genArg trElem)
          let valElems :: [b]
              valElems =
                args <&> \case
                  Constant _ (Some (ValueOf _ valElem')) -> unsafeCoerce valElem'
                  _                                      -> error "genArg: encountered non-Constant term"
          pure
            ( Constant () (someValueOf (DefaultUniApply DefaultUniProtoList uniElem) valElems),
              show argStrings
            )
        _ -> error "genArg: encountered non-Constant term"
  -- Descend upon `Opaque`
  | Just [_, SomeTypeRep tr'] <- matchTyCon @Opaque tr = genArg tr'
  -- Descend upon `SomeConstant`
  | Just [_, SomeTypeRep tr'] <- matchTyCon @SomeConstant tr = genArg tr'
  -- In the current implementation, all type variables are instantiated
  -- to `Integer` (TODO: change this).
  | Just _ <- matchTyCon' "PlutusCore.Builtin.Polymorphism" "TyVarRep" tr =
      pure . mkArg =<< genInteger
  | otherwise =
      error $
        "genArg: I don't know how to generate builtin arguments of this type: " <> show tr

mkArg :: (Contains DefaultUni a, Show a) => a -> (Term, String)
mkArg a = (Constant () (someValue a), show a)

-- | If the given `TypeRep`'s `TyCon` is @con@, return its type arguments.
matchTyCon :: forall con a. (Typeable con) => TypeRep a -> Maybe [SomeTypeRep]
matchTyCon tr = if con == con' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    con' = typeRepTyCon (typeRep @con)

-- | If the given `TypeRep`'s `TyCon` matches the given module and name, return its type arguments.
matchTyCon' :: forall a. String -> String -> TypeRep a -> Maybe [SomeTypeRep]
matchTyCon' modu name tr = if modu == modu' && name == name' then Just args else Nothing
  where
    (con, args) = splitTyConApp (SomeTypeRep tr)
    modu' = tyConModule con
    name' = tyConName con

type family Head a where
  Head (x ': xs) = x

----------------------------------------------------------
-- Generators

genInteger :: Gen Integer
genInteger = fromIntegral @Int64 <$> Gen.enumBounded

genByteString :: Gen BS.ByteString
genByteString = Gen.utf8 (Range.linear 0 100) Gen.enumBounded

genText :: Gen Text
genText = Gen.text (Range.linear 0 100) Gen.enumBounded

genData :: Int -> Gen Data
genData depth =
  Gen.choice $
    [genI, genB]
      <> [ genRec | depth > 1, genRec <-
                                 [ genList (depth - 1),
                                   genMap (depth - 1),
                                   genConstr (depth - 1)
                                 ]
         ]

genI :: Gen Data
genI = I <$> genInteger

genB :: Gen Data
genB = B <$> genByteString

genList :: Int -> Gen Data
genList depth = List <$> Gen.list (Range.linear 0 5) (genData (depth - 1))

genMap :: Int -> Gen Data
genMap depth =
  Map
    <$> Gen.list
      (Range.linear 0 5)
      ((,) <$> genData (depth - 1) <*> genData (depth - 1))

genConstr :: Int -> Gen Data
genConstr depth =
  Constr <$> genInteger
    <*> Gen.list
      (Range.linear 0 5)
      (genData (depth - 1))

test_evaluation :: TestTree
test_evaluation =
  testGroup
    "evaluation"
    [ test_machines,
      test_builtinsDon'tThrow
    ]
