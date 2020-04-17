{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}

module Arithmetic.Interpreter where

import Data.Text (Text)
import qualified Data.Text as T

type Info = Text

data Term =
  TmTrue Info
  | TmFalse Info
  | TmIf Info Term Term Term
  | TmZero Info
  | TmSucc Info Term
  | TmPred Info Term
  | TmIsZero Info Term
  deriving (Show, Eq)

isNumeric :: Term -> Bool
isNumeric (TmZero _) = True
isNumeric (TmSucc _ t) = isNumeric t
isNumeric (TmPred _ t) = isNumeric t
isNumeric _ = False

isVal :: Term -> Bool
isVal (TmTrue _) = True
isVal (TmFalse _) = True
isVal t | isNumeric t = True
        | otherwise = False

data Step a = Continue a
            | Halt a
  deriving (Show, Eq, Functor)

-- | A single step of small-step semantic evaluation
-- Returns Left when no rule applies, and Right when a step has been taken
smallStep :: Term -> Step Term
smallStep t@(TmTrue _) = Halt t
smallStep t@(TmFalse _) = Halt t
smallStep (TmIf _ (TmTrue _) t _) = Continue t
smallStep (TmIf _ (TmFalse _) _ f) = Continue f
smallStep tif@(TmIf i tst t f) =
    case smallStep tst of
      Continue tst' -> Continue (TmIf i tst' t f)
      -- differentiate between halting because the boolean is fully
      -- evaluted and because it's not a real term
      -- This is sort of the provenance of eval, but we're doing it
      -- here to make the logic work
      Halt (TmTrue _) -> Continue t
      Halt (TmFalse _) -> Continue f
      Halt _ -> Halt tif
smallStep t@(TmZero _) = Halt t
smallStep (TmSucc i t) = TmSucc i <$> smallStep t
smallStep (TmPred i t) = TmPred i <$> smallStep t
smallStep (TmIsZero i (TmZero _)) = Continue (TmTrue i)
smallStep t@(TmIsZero i (TmSucc _ n)) =
    if isNumeric n
      then Halt (TmFalse i)
      else Halt t
smallStep (TmIsZero i t) = TmIsZero i <$> smallStep t

eval :: Term -> Either Text Term
eval t = case smallStep t of
           Halt r -> if isVal r
                       then Right r
                       else Left $ "Not a valid term " <> (T.pack . show) r
           Continue s -> eval s
