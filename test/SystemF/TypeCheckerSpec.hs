{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module SystemF.TypeCheckerSpec where

import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Functor.Identity (runIdentity)
import SystemF.TypeChecker
import Test.HUnit (Test(..), assertEqual)

tests :: Test
tests = TestLabel "system f" $ TestList
    [ TestLabel "typecheck variable" $ TestCase variables
    , TestLabel "typecheck lambda" $ TestCase lambdas
    , TestLabel "typecheck application" $ TestCase applications
    , TestLabel "forall" $ TestCase foralls
    , TestLabel "existential" $ TestCase existentials
    ]

variables :: IO ()
variables = do
  assertEqual "typeof var"
    (Right TyBool)
    (runIdentity
      . flip runReaderT [("x", VarBind TyBool)]
      . runExceptT
      . (typeOf @TypeChecker)
      $ TmVar (DeBruijn 0))
  assertEqual "typeof undefined var"
    (Left "Var not found")
    (typecheck $ TmVar (DeBruijn 0))

lambdas :: IO ()
lambdas = do
  assertEqual "typeof identity"
    (Right $ TyFn TyBool TyBool)
    (typecheck $ TmLambda "x" TyBool (TmVar $ DeBruijn 0))
  assertEqual "typeof constant function"
    (Right $ TyFn TyBool TyBool)
    (typecheck $ TmLambda "x" TyBool TmFalse)
  assertEqual "typeof nested function"
    (Right $ TyFn TyBool (TyFn TyBool TyBool))
    (typecheck $ TmLambda "x" TyBool $ TmLambda "y" TyBool (TmVar $ DeBruijn 1))
  assertEqual "typeof accepting a function"
    (Right $ TyFn (TyFn TyBool TyBool) TyBool)
    (typecheck $ TmLambda "f" (TyFn TyBool TyBool) $ TmApp (TmVar $ DeBruijn 0) TmTrue)

applications :: IO ()
applications = do
  assertEqual "typeof apply bool to bool fails"
    (Left "Expected function type, but got TyBool")
    (typecheck $ TmApp TmTrue TmFalse)
  assertEqual "type mismatch in function argument"
    (Left "Type mismatch: expected TyBool but got TyFn TyBool TyBool")
    (typecheck $ TmApp (TmLambda "b" TyBool $ TmTrue) (TmLambda "c" TyBool $ TmFalse))
  assertEqual "typeof application is type of body"
    (Right TyBool)
    (typecheck $ TmApp (TmLambda "b" TyBool $ TmTrue) (TmFalse))
  assertEqual "typeof application body uses type of argument"
    (Right $ TyFn TyBool TyBool)
    (typecheck $ TmApp (TmLambda "b" TyBool $ TmLambda "c" TyBool $ TmVar (DeBruijn 1))
                        TmTrue)

foralls :: IO ()
foralls = do
  assertEqual "polymorphic id"
    (Right tyId)
    (typecheck tmId)
  assertEqual "polymorphic const"
    (Right tyConst)
    (typecheck tmConst)
  assertEqual "specializing id to Bool"
    (Right $ TyFn TyBool TyBool)
    (typecheck $ TmTApp tmId TyBool)
  assertEqual "const id true"
    (Right tyId)
    (typecheck $ TmApp (TmApp (TmTApp (TmTApp tmConst tyId) TyBool) tmId) TmTrue)

tmId :: Term
tmId =
  TmTAbs "a" $
    TmLambda "x" (TyVar $ DeBruijn 0) $
      TmVar $ DeBruijn 0

tyId :: Typ
tyId = TyAll "a" $ TyFn (TyVar $ DeBruijn 0) (TyVar $ DeBruijn 0)

tmConst :: Term
tmConst =
  TmTAbs "a" $
    TmTAbs "b" $
      TmLambda "x" (TyVar (DeBruijn 1)) $
        TmLambda "y" (TyVar (DeBruijn 1)) $
          TmVar (DeBruijn 1)

tyConst :: Typ
tyConst =
  TyAll "a" $
    TyAll "b" $
      TyFn (TyVar $ DeBruijn 1)
            (TyFn (TyVar $ DeBruijn 0)
                  (TyVar $ DeBruijn 1))

existentials :: IO ()
existentials = do
  assertEqual "trivial existential"
    (Right tyExId)
    (typecheck $ tmExId)
  assertEqual "unpack existential"
    (Right TyBool)
    (typecheck $ TmUnpack "typ" "tm" tmExId $ TmApp (TmSnd $ TmVar $ DeBruijn 0)
                                                    (TmFst $ TmVar $ DeBruijn 0))

tmExId :: Term
tmExId =
  TmPack
    TyBool
    (TmPair TmTrue (TmLambda "a" TyBool $ (TmVar $ DeBruijn 0)))
    (TySome "a" $ TyPair (TyVar $ DeBruijn 0) $ TyFn (TyVar $ DeBruijn 0) TyBool)

tyExId :: Typ
tyExId =
    TySome "a"
      $ TyPair (TyVar $ DeBruijn 0)
               (TyFn (TyVar $ DeBruijn 0) TyBool)

