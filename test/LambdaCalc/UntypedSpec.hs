{-# LANGUAGE OverloadedStrings #-}

module LambdaCalc.UntypedSpec where

import Prelude hiding (and)
import qualified Data.Text as T
import LambdaCalc.Untyped
import Test.HUnit (Test(..), assertEqual)

tests :: Test
tests = TestLabel "untyped lambda calculus" $ TestList
    [ TestLabel "values" $ TestCase evalValues
    , TestLabel "booleans" $ TestCase evalBoolExprs
    , TestLabel "pairs" $ TestCase evalPairExprs
    , TestLabel "numbers" $ TestCase evalNumExprs
    , TestLabel "recursion" $ TestCase evalRecursionExprs
    ]

identity :: Term
identity = TmLambda "x" (TmVar 0 $ DeBruijn 0)

true :: Term
true = TmLambda "t"
       $ TmLambda "f"
         $ TmVar 1 $ DeBruijn 1

false :: Term
false = TmLambda "t"
        $ TmLambda "f"
          $ TmVar 1 $ DeBruijn 0

evalValues :: IO ()
evalValues = do
    assertEqual "eval identity"
      (Right identity)
      (eval [] identity)
    assertEqual "eval true"
      (Right true)
      (eval [] true)
    assertEqual "eval false"
      (Right false)
      (eval [] false)
    assertEqual "eval and"
      (Right and)
      (eval [] and)

and :: Term
and = TmLambda "b"
      $ TmLambda "c"
        $ TmApp
            (TmApp (TmVar 1 $ DeBruijn 1) (TmVar 1 $ DeBruijn 0))
            false

ifL :: Term
ifL = TmLambda "b"
      $ TmLambda "t"
        $ TmLambda "f"
          $ TmApp (TmApp (TmApp (TmVar 3 $ DeBruijn 2)
                            (TmVar 3 $ DeBruijn 1))
                      (TmVar 3 $ DeBruijn 0)
                  )
                  zero


evalBoolExprs :: IO ()
evalBoolExprs = do
    assertEqual "identity true"
      (Right true)
      (eval [] $ TmApp identity true)
    assertEqual "identity false"
      (Right false)
      (eval [] $ TmApp identity false)
    assertEqual "and true true"
      (Right true)
      (eval [] $ TmApp (TmApp and true) true)
    assertEqual "and false false"
      (Right false)
      (eval [] $ TmApp (TmApp and false) false)
    assertEqual "and true false"
      (Right false)
      (eval [] $ TmApp (TmApp and true) false)
    assertEqual "if true"
      (Right zero)
      (eval [] $ TmApp (TmApp (TmApp ifL true) (TmLambda "_" zero)) (TmLambda "_" one))
    assertEqual "if false"
      (Right one)
      (eval [] $ TmApp (TmApp (TmApp ifL false) (TmLambda "_" zero)) (TmLambda "_" one))

pair :: Term
pair = TmLambda "f"
       $ TmLambda "s"
         $ TmLambda "b"
           $ TmApp (TmApp (TmVar 3 $ DeBruijn 0)
                          (TmVar 3 $ DeBruijn 2))
                   (TmVar 3 $ DeBruijn 1)

fstL :: Term
fstL = TmLambda "p" $ TmApp (TmVar 1 $ DeBruijn 0) true

sndL :: Term
sndL = TmLambda "p" $ TmApp (TmVar 1 $ DeBruijn 0) false

evalPairExprs :: IO ()
evalPairExprs = do
    assertEqual "fst is first"
      (Right true)
      (eval [] $ TmApp fstL (TmApp (TmApp pair true) false))
    assertEqual "snd is second"
      (Right false)
      (eval [] $ TmApp sndL (TmApp (TmApp pair true) false))

zero :: Term
zero = TmLambda "s" (TmLambda "z" (TmVar 2 $ DeBruijn 0))

succL :: Term
succL = TmLambda "n"
       $ TmLambda "s"
         $ TmLambda "z" $ TmApp (TmVar 3 $ DeBruijn 1)
                                (TmApp (TmApp (TmVar 3 $ DeBruijn 2) (TmVar 3 $ DeBruijn 1))
                                       (TmVar 3 $ DeBruijn 0))

iszero :: Term
iszero = TmLambda "n" (TmApp (TmApp (TmVar 1 $ DeBruijn 0) (TmLambda "x" false))
                             true)

plus :: Term
plus = TmLambda "m"
       $ TmLambda "n"
             $ TmApp (TmApp (TmVar 2 $ DeBruijn 1)
                            succL)
                     (TmVar 2 $ DeBruijn 0)

times :: Term
times = TmLambda "m"
        $ TmLambda "n"
          $ TmApp (TmApp (TmVar 2 $ DeBruijn 1)
                         (TmApp plus (TmVar 2 $ DeBruijn 0)))
                  zero

predL :: Term
predL = TmLambda "m"
        $ TmApp fstL
          $ TmApp (TmApp (TmVar 1 $ DeBruijn 0) ss) zz
   where ss = TmLambda "p"
               $ TmApp (TmApp pair (TmApp sndL (TmVar 1 $ DeBruijn 0)))
                       (TmApp succL (TmApp sndL (TmVar 1 $ DeBruijn 0)))
         zz = TmApp (TmApp pair zero) zero

minus :: Term
minus = TmLambda "m"
        $ TmLambda "n"
              $ TmApp (TmApp (TmVar 2 $ DeBruijn 0)
                             predL)
                      (TmVar 2 $ DeBruijn 1)

equalL :: Term
equalL = TmLambda "m"
        $ TmLambda "n"
          $ TmApp (TmApp and (TmApp iszero $ minus' 0 1)) (TmApp iszero $ minus' 1 0)
  where minus' db1 db2 = TmApp (TmApp minus (TmVar 2 $ DeBruijn db1)) (TmVar 2 $ DeBruijn db2)

one, two, three, four, five, six :: Term
one = mustBeRight $ eval [] $ TmApp succL zero
two = mustBeRight $ eval [] $ TmApp succL one
three = mustBeRight $ eval [] $ TmApp succL two
four = mustBeRight $ eval [] $ TmApp succL three
five = mustBeRight $ eval [] $ TmApp succL four
six = mustBeRight $ eval [] $ TmApp succL five

mustBeRight :: Either T.Text Term -> Term
mustBeRight (Right x) = x
mustBeRight (Left x) = error . T.unpack $ "Expected right, but got Left " <> x

evalNumExprs :: IO ()
evalNumExprs = do
    assertEqual "zero is zero"
      (Right true)
      (eval [] $ TmApp iszero zero)
    assertEqual "one is not zero"
      (Right false)
      (eval [] $ TmApp iszero (TmApp succL zero))
    assertEqual "pred . succ = id"
      (Right true)
      (eval [] $ TmApp iszero (TmApp predL (TmApp succL zero)))
    assertEqual "addition"
      (Right five)
      (eval [] $ TmApp (TmApp plus two) three)
    assertEqual "subtraction"
      (Right two)
      (eval [] $ TmApp (TmApp minus five) three)
    assertEqual "multiplication"
      (Right six)
      (eval [] $ TmApp (TmApp times two) three)
    assertEqual "equality"
      (Right true)
      (eval [] $ TmApp (TmApp equalL two) two)
    assertEqual "not equality"
      (Right false)
      (eval [] $ TmApp (TmApp equalL two) three)
    assertEqual "if equal"
      (Right one)
      (eval [] $ TmApp (TmApp (TmApp ifL
                                     (TmApp (TmApp equalL zero) zero))
                              (TmLambda "_" one))
                       (TmLambda "_" two))
    assertEqual "if not equal"
      (Right two)
      (eval [] $ TmApp (TmApp (TmApp ifL
                                     (TmApp (TmApp equalL zero) one))
                              (TmLambda "_" one))
                       (TmLambda "_" two))

fix :: Term
fix = TmLambda "f"
      $ TmApp
        (TmLambda "x"
          $ TmApp (TmVar 2 $ DeBruijn 1)
                  (TmLambda "y" $ TmApp (TmApp (TmVar 3 $ DeBruijn 1)
                                               (TmVar 3 $ DeBruijn 1))
                                        (TmVar 3 $ DeBruijn 0))
        )
        (TmLambda "x"
          $ TmApp (TmVar 2 $ DeBruijn 1)
                  (TmLambda "y" $ TmApp (TmApp (TmVar 3 $ DeBruijn 1)
                                               (TmVar 3 $ DeBruijn 1))
                                        (TmVar 3 $ DeBruijn 0))
        )

factorialF :: Term
factorialF = TmLambda "f"
             $ TmLambda "x"
               (TmApp (TmApp (TmApp ifL (TmApp (TmApp equalL (TmVar 2 $ DeBruijn 0)) zero))
                              (TmLambda "_" $ one))
                      (TmLambda "_" $
                        (TmApp (TmApp times (TmVar 2 $ DeBruijn 1))
                              (TmApp (TmVar 2 $ DeBruijn 2)
                                      (TmApp predL (TmVar 2 $ DeBruijn 1))))))

factorial :: Term
factorial = TmApp fix factorialF

evalRecursionExprs :: IO ()
evalRecursionExprs = do
    assertEqual "factorial of 1"
      (Right one)
      (eval [] $ TmApp factorial one)
    assertEqual "factorial of 3"
      (Right six)
      (eval [] $ TmApp factorial three)
