{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LambdaCalc.SimplyTyped where

import Data.Maybe (listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T

data Binding =
    NameBind
    | VarBind Typ

type Var = Text
type Context = [(Var, Binding)]

addBinding :: Context -> Var -> Binding -> Context
addBinding ctx var binding = (var,  binding) : ctx

getTypeFromContext :: Context -> DeBruijn -> Either Var Typ
getTypeFromContext ctx (DeBruijn idx) =
    case snd <$> safeIndex idx ctx of
      Nothing -> Left $ "Var not found"
      Just NameBind -> Left $ "Var not a variable binding"
      Just (VarBind a) -> Right a

data Typ =
    TyFn Typ Typ
    | TyBool
    deriving (Eq, Show)

newtype DeBruijn = DeBruijn { unDeBruijn :: Int }
                   deriving newtype (Show, Eq)

data Term =
    TmVar Int DeBruijn
    | TmLambda Text Typ Term
    | TmApp Term Term
    | TmTrue
    | TmFalse
    | TmIf Term Term Term

typeOf :: Context -> Term -> Either Text Typ
typeOf ctx (TmVar _ idx) =  getTypeFromContext ctx idx
typeOf ctx (TmLambda var a term) =
    let
      ctx' = addBinding ctx var (VarBind a)
    in
      TyFn a <$> typeOf ctx' term
typeOf ctx (TmApp f x) = do
    fnTyp <- typeOf ctx f
    argTyp <- typeOf ctx x
    case fnTyp of
      TyFn fm to -> if fm == argTyp
                    then pure to
                    else Left $ "Type mismatch: expected "
                                <> tshow fm <> " but got " <> tshow argTyp
      notFn -> Left $ "Expected function type, but got " <> tshow notFn
typeOf _ TmTrue = pure TyBool
typeOf _ TmFalse = pure TyBool
typeOf ctx (TmIf test true false) = do
    tyTest <- typeOf ctx test
    if tyTest == TyBool
      then pure ()
      else Left "Error in If: test must be a Boolean"
    tyTrue <- typeOf ctx true
    tyFalse <- typeOf ctx false
    if tyTrue == tyFalse
      then pure tyTrue
      else Left $ "TypeError in If: branches must be the same type, but are "
                  <> tshow tyTrue <> " and " <> tshow tyFalse

safeIndex :: Int -> [a] -> Maybe a
safeIndex idx = listToMaybe . drop (idx - 1)

tshow :: Show a => a -> Text
tshow = T.pack . show
