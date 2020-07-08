{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module LambdaCalc.SimplyTypedSpec where

import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (runReaderT)
import Control.Monad.State (evalStateT)
import Data.Functor.Identity (runIdentity)
import LambdaCalc.SimplyTyped
import Test.HUnit (Test(..), assertEqual)

tests :: Test
tests = TestLabel "simply typed lambda calculus" $ TestList
    [ TestLabel "typecheck basic terms" $ TestCase basicTerms
    , TestLabel "typecheck variable" $ TestCase variables
    , TestLabel "typecheck lambda" $ TestCase lambdas
    , TestLabel "typecheck application" $ TestCase applications
    , TestLabel "typecheck if" $ TestCase ifs
    , TestLabel "typecheck product" $ TestCase products
    , TestLabel "typecheck sum" $ TestCase sums
    ]

basicTerms :: IO ()
basicTerms = do
    assertEqual "typeof True"
      (Right TyBool)
      (typecheck TmTrue)
    assertEqual "typeof False"
      (Right TyBool)
      (typecheck TmFalse)
    assertEqual "typeof String"
      (Right TyString)
      (typecheck $ TmStr "hello, world")
    assertEqual "typeof Int"
      (Right TyInt)
      (typecheck $ TmInt 42)
    assertEqual "typeof Unit"
      (Right TyUnit)
      (typecheck $ TmUnit)
    assertEqual "typeof Pair Int Int"
      (Right $ TyPair TyInt TyInt)
      (typecheck $ TmPair (TmInt 5) (TmInt 5))

variables :: IO ()
variables = do
    assertEqual "typeof var"
      (Right TyBool)
      (runIdentity
       . flip runReaderT [("x", VarBind TyBool)]
       . flip evalStateT (TypeEnv [])
       . runExceptT
       . (typeOf @TypeChecker)
       $ TmVar 1 (DeBruijn 0))
    assertEqual "typeof undefined var"
      (Left "Var not found")
      (typecheck $ TmVar 1 (DeBruijn 0))

lambdas :: IO ()
lambdas = do
    assertEqual "typeof identity"
      (Right $ TyFn TyBool TyBool)
      (typecheck $ TmLambda "x" TyBool (TmVar 1 $ DeBruijn 0))
    assertEqual "typeof constant function"
      (Right $ TyFn TyBool TyBool)
      (typecheck $ TmLambda "x" TyBool TmFalse)
    assertEqual "typeof nested function"
      (Right $ TyFn TyBool (TyFn TyBool TyBool))
      (typecheck $ TmLambda "x" TyBool $ TmLambda "y" TyBool (TmVar 2 $ DeBruijn 1))
    assertEqual "typeof accepting a function"
      (Right $ TyFn (TyFn TyBool TyBool) TyBool)
      (typecheck $ TmLambda "f" (TyFn TyBool TyBool) $ TmApp (TmVar 1 $ DeBruijn 0) TmTrue)

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
      (typecheck $ TmApp (TmLambda "b" TyBool $ TmLambda "c" TyBool $ TmVar 2 (DeBruijn 1))
                         TmTrue)

ifs :: IO ()
ifs = do
    assertEqual "typeof if all bools"
      (Right TyBool)
      (typecheck $ TmIf TmTrue TmTrue TmFalse)
    assertEqual "typeof if with lambdas"
      (Right $ TyFn TyBool TyBool)
      (typecheck $ TmIf TmTrue (TmLambda "x" TyBool $ TmTrue) (TmLambda "x" TyBool $ TmFalse))
    assertEqual "typeof if test resolves to bool"
      (Right TyBool)
      (typecheck $ TmIf (TmApp (TmLambda "x" TyBool $ TmVar 1 (DeBruijn 0)) TmTrue)
                        TmTrue
                        TmFalse)
    assertEqual "typeof if fails when test is not boolean"
      (Left "Error in If: test must be a Boolean")
      (typecheck $ TmIf (TmLambda "x" TyBool $ TmTrue) TmTrue TmFalse)
    assertEqual "typeof if fails when branches have different types"
      (Left "TypeError in If: branches must be the same type, but are TyBool and TyFn TyBool TyBool")
      (typecheck $ TmIf TmTrue TmFalse (TmLambda "x" TyBool $ TmTrue))

products :: IO ()
products = do
  let cat = TmMkProd [ ("name", TmStr "houdini")
                     , ("age", TmInt 13)
                     , ("favoriteFood", TmStr "butter")
                     ]
      catType = TyProduct [("name", TyString), ("age", TyInt), ("favoriteFood", TyString)]
  assertEqual "typeof product"
    (Right $ catType)
    (typecheck cat)
  assertEqual "typeof projection"
    (Right $ TyInt)
    (typecheck $ TmProjProd "age" cat)
  assertEqual "typeof update"
    (Right catType)
    (typecheck $ TmUpdateProd "favoriteFood" (TmStr "turkey") cat)
  assertEqual "type error on nonsensical update"
    (Left "type mismatch: expected TyString but got TyInt")
    (typecheck $ TmUpdateProd "favoriteFood" (TmInt 5) cat)

sums :: IO ()
sums = do
  let variants = [("justInt", TyInt), ("noInt", TyUnit)]
      maybeInt = TySum variants
      withMaybe t = TmSequence $ [(TmDeclareSum variants), t]
  assertEqual "typeof sum variant"
    (Right maybeInt)
    (typecheck $ withMaybe $ TmCall "justInt" (TmInt 5))
  assertEqual "type error when injecting wrong type"
    (Left "type mismatch: expected TyIntbut got TyStringwhen calling justInt")
    (typecheck $ withMaybe $ TmCall "justInt" (TmStr "hello"))
  assertEqual "typeof match statement"
    (Right TyInt)
    (typecheck $ withMaybe
      $ TmMatchSum (TmCall "noInt" TmUnit)
                   [ ("justInt", TmLambda "x" TyInt (TmVar 1 $ DeBruijn 0))
                   , ("noInt", TmLambda "_" TyUnit (TmInt 0))
                   ])
  assertEqual "type error when match branch expects incorrect type"
    (Left "type mismatch: expected match arm to take TyUnit but actually takes TyInt")
    (typecheck $ withMaybe
      $ TmMatchSum (TmCall "noInt" TmUnit)
                   [ ("justInt", TmLambda "x" TyInt (TmVar 1 $ DeBruijn 0))
                   , ("noInt", TmLambda "_" TyInt (TmInt 0))
                   ])
  assertEqual "type error when branches have different types"
    (Left "All branches of a match statement should have the same type, but the following types were found [TyInt,TyString]")
    (typecheck $ withMaybe
      $ TmMatchSum (TmCall "noInt" TmUnit)
                   [ ("justInt", TmLambda "x" TyInt (TmVar 1 $ DeBruijn 0))
                   , ("noInt", TmLambda "_" TyUnit (TmStr "whoops"))
                   ])
