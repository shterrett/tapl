{-# LANGUAGE OverloadedStrings #-}

module LambdaCalc.SimplyTypedSpec where

import LambdaCalc.SimplyTyped
import Test.HUnit (Test(..), assertEqual)

tests :: Test
tests = TestLabel "simply typed lambda calculus" $ TestList
    [ TestLabel "typecheck basic terms" $ TestCase basicTerms
    , TestLabel "typecheck variable" $ TestCase variables
    , TestLabel "typecheck lambda" $ TestCase lambdas
    , TestLabel "typecheck application" $ TestCase applications
    , TestLabel "typecheck if" $ TestCase ifs
    ]

basicTerms :: IO ()
basicTerms = do
    assertEqual "typeof True"
      (Right TyBool)
      (typeOf [] TmTrue)
    assertEqual "typeof False"
      (Right TyBool)
      (typeOf [] TmFalse)

variables :: IO ()
variables = do
    assertEqual "typeof var"
      (Right TyBool)
      (typeOf [("x", VarBind TyBool)] $ TmVar 1 (DeBruijn 0))
    assertEqual "typeof undefined var"
      (Left "Var not found")
      (typeOf [] $ TmVar 1 (DeBruijn 0))

lambdas :: IO ()
lambdas = do
    assertEqual "typeof identity"
      (Right $ TyFn TyBool TyBool)
      (typeOf [] $ TmLambda "x" TyBool (TmVar 1 $ DeBruijn 0))
    assertEqual "typeof constant function"
      (Right $ TyFn TyBool TyBool)
      (typeOf [] $ TmLambda "x" TyBool TmFalse)
    assertEqual "typeof nested function"
      (Right $ TyFn TyBool (TyFn TyBool TyBool))
      (typeOf [] $ TmLambda "x" TyBool $ TmLambda "y" TyBool (TmVar 2 $ DeBruijn 1))
    assertEqual "typeof accepting a function"
      (Right $ TyFn (TyFn TyBool TyBool) TyBool)
      (typeOf [] $ TmLambda "f" (TyFn TyBool TyBool) $ TmApp (TmVar 1 $ DeBruijn 0) TmTrue)

applications :: IO ()
applications = do
    assertEqual "typeof apply bool to bool fails"
      (Left "Expected function type, but got TyBool")
      (typeOf [] $ TmApp TmTrue TmFalse)
    assertEqual "type mismatch in function argument"
      (Left "Type mismatch: expected TyBool but got TyFn TyBool TyBool")
      (typeOf [] $ TmApp (TmLambda "b" TyBool $ TmTrue) (TmLambda "c" TyBool $ TmFalse))
    assertEqual "typeof application is type of body"
      (Right TyBool)
      (typeOf [] $ TmApp (TmLambda "b" TyBool $ TmTrue) (TmFalse))
    assertEqual "typeof application body uses type of argument"
      (Right $ TyFn TyBool TyBool)
      (typeOf [] $ TmApp (TmLambda "b" TyBool $ TmLambda "c" TyBool $ TmVar 2 (DeBruijn 1))
                         TmTrue)

ifs :: IO ()
ifs = do
    assertEqual "typeof if all bools"
      (Right TyBool)
      (typeOf [] $ TmIf TmTrue TmTrue TmFalse)
    assertEqual "typeof if with lambdas"
      (Right $ TyFn TyBool TyBool)
      (typeOf [] $ TmIf TmTrue (TmLambda "x" TyBool $ TmTrue) (TmLambda "x" TyBool $ TmFalse))
    assertEqual "typeof if test resolves to bool"
      (Right TyBool)
      (typeOf [] $ TmIf (TmApp (TmLambda "x" TyBool $ TmVar 1 (DeBruijn 0)) TmTrue)
                        TmTrue
                        TmFalse)
    assertEqual "typeof if fails when test is not boolean"
      (Left "Error in If: test must be a Boolean")
      (typeOf [] $ TmIf (TmLambda "x" TyBool $ TmTrue) TmTrue TmFalse)
    assertEqual "typeof if fails when branches have different types"
      (Left "TypeError in If: branches must be the same type, but are TyBool and TyFn TyBool TyBool")
      (typeOf [] $ TmIf TmTrue TmFalse (TmLambda "x" TyBool $ TmTrue))
