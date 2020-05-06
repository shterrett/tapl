{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LambdaCalc.Untyped where

import Data.Text (Text)
import qualified Data.Text as T

newtype DeBruijn = DeBruijn { unDeBruijn :: Int }
                   deriving newtype (Show, Eq)

data Term =
    TmVar Int DeBruijn
    | TmLambda Text Term
    | TmApp Term Term
    deriving stock (Show)

instance Eq Term where
    (TmVar _ x) == (TmVar _ y) = x == y
    (TmLambda v1 t1) == (TmLambda v2 t2) = v1 == v2 && t1 == t2
    (TmApp t11 t12) == (TmApp t21 t22) = t11 == t21 && t12 == t22
    _ == _ = False

data Binding = Binding
             deriving (Show)
type Context = [(Text, Binding)]

printTerm :: Context -> Term -> Text
printTerm ctx (TmLambda var t) =
    let
      (var', ctx') = pickFreshName ctx var
    in
      "(λ" <> var' <> ". " <> printTerm ctx' t <> ")"
printTerm ctx (TmVar _ (DeBruijn idx)) = maybe "[bad index]" fst $ at idx ctx
printTerm ctx (TmApp t1 t2) = "(" <> printTerm ctx t1 <> " " <> printTerm ctx t2 <> ")"

at :: Int -> [a] -> Maybe a
at _ [] = Nothing
at 0 (a:_) = Just a
at n (_:as) = at (n - 1) as

pickFreshName :: Context -> Text -> (Text, Context)
pickFreshName [] var = (var, [(var, Binding)])
pickFreshName ctx var =
       if var `elem` (fst <$> ctx)
         then pickFreshName ctx (var <> "'")
         else (var, (var, Binding) : ctx)

termShift :: Int -> Term -> Term
termShift shft term = walk 0 term
  where walk :: Int -> Term -> Term
        walk cut (TmVar l (DeBruijn idx)) =
          if idx >= cut
            then TmVar (l + shft) (DeBruijn $ idx + shft)
            else TmVar (l + shft) (DeBruijn idx)
        walk cut (TmLambda var t) = TmLambda var (walk (cut + 1) t)
        walk cut (TmApp t1 t2) = TmApp (walk cut t1) (walk cut t2)

termSub :: DeBruijn -> Term -> Term -> Term
termSub (DeBruijn idx) val target = walk 0 target
  where walk :: Int -> Term -> Term
        walk shft tmvar@(TmVar _ (DeBruijn v)) =
          if v == idx + shft
            then val
            else tmvar
        walk shft (TmLambda var t) = TmLambda var $ walk (shft + 1) t
        walk shft (TmApp t1 t2) = TmApp (walk shft t1) (walk shft t2)

termSubTop :: Term -> Term -> Term
termSubTop s t = termShift (-1) $ termSub (DeBruijn 0) (termShift 1 s) t

isValue :: Context -> Term -> Bool
isValue _ (TmLambda _ _) = True
isValue _ _ = False

data Step a = Continue a
            | Halt a
    deriving stock (Show, Eq, Functor)

extract :: Step a -> a
extract (Continue a) = a
extract (Halt a) = a

smallStep :: Context -> Term -> Step Term
smallStep ctx (TmApp lam@(TmLambda _ body) t)
  | isValue ctx t = Continue $ termSubTop t body
  | otherwise = TmApp lam <$> smallStep ctx t
smallStep ctx (TmApp t1 t2) = flip TmApp t2 <$> smallStep ctx t1
smallStep _ t = Halt t

eval :: Context -> Term -> Either Text Term
eval ctx t =
    case smallStep ctx t of
      Halt r -> if isValue ctx r
                  then Right r
                  else Left $ "Not a valid term " <> (T.pack . show) r
      Continue r -> eval ctx r
