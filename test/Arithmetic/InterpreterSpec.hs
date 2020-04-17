{-# LANGUAGE OverloadedStrings #-}

module Arithmetic.InterpreterSpec where

import Arithmetic.Interpreter
import Data.Text (Text)
import qualified Data.Text as T
import Test.HUnit (Test(..), assertEqual, assertFailure)

tests :: Test
tests = TestList
    [ TestLabel "values" $ TestCase evalValues
    , TestLabel "illegal terms" $ TestCase illegalTerms
    , TestLabel "reduces if" $ TestCase ifTerms
    ]

info :: Info
info = ""

evalValues :: IO ()
evalValues = do
    assertEqual "eval True"
                (Right $ TmTrue info)
                (eval $ TmTrue info)
    assertEqual "eval False"
                (Right $ TmFalse info)
                (eval $ TmFalse info)
    assertEqual "eval Zero"
                (Right $ TmZero info)
                (eval $ TmZero info)
    assertEqual "eval Succ"
                (Right $ TmSucc info (TmZero info))
                (eval $ TmSucc info (TmZero info))

illegalTerms :: IO ()
illegalTerms = do
    assertLeft "successor of boolean"
               (eval $ TmSucc info (TmTrue info))
    assertLeft "predecessor of boolean"
               (eval $ TmPred info (TmFalse info))
    assertLeft "if number"
              (eval $ TmIf info (TmZero info) (TmTrue info) (TmFalse info))
    assertLeft "if succ"
              (eval $ TmIf info (TmSucc info (TmZero info))
                                (TmTrue info)
                                (TmFalse info))

ifTerms :: IO ()
ifTerms = do
    assertEqual "if true"
                (Right $ TmTrue info)
                (eval $ (TmIf info (TmTrue info)
                                   (TmTrue info)
                                   (TmFalse info)))
    assertEqual "if false"
                (Right $ TmFalse info)
                (eval $ (TmIf info (TmFalse info)
                                   (TmTrue info)
                                   (TmFalse info)))
    assertEqual "if is zero"
                (Right $ TmTrue info)
                (eval $ (TmIf info (TmIsZero info (TmZero info))
                                   (TmTrue info)
                                   (TmFalse info)))
    assertEqual "nested if"
                (Right $ TmZero info)
                (eval $ (TmIf info (TmIsZero info (TmSucc info (TmZero info)))
                                   (TmFalse info)
                                   (TmIf info (TmTrue info)
                                              (TmZero info)
                                              (TmSucc info (TmZero info)))))

assertLeft :: Text -> Either a b -> IO ()
assertLeft m e = case e of
                   Left _ -> pure ()
                   Right _ -> assertFailure (T.unpack m)
