{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LambdaCalc.SimplyTyped where

import Control.Monad.Except (ExceptT, MonadError, throwError)
import Control.Monad.Reader (ReaderT, reader, local)
import Data.Functor.Identity (Identity)
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T

data Binding =
    NameBind
    | VarBind Typ
  deriving (Show)

type Var = Text
type Context = [(Var, Binding)]

addBinding' :: Context -> Var -> Binding -> Context
addBinding' ctx var binding = (var,  binding) : ctx

getTypeFromContext :: (WithContext m, MonadError Text m) => DeBruijn -> m Typ
getTypeFromContext (DeBruijn idx) = do
    ctx <- askContext
    case snd <$> safeIndex idx ctx of
      Nothing -> throwError "Var not found"
      Just NameBind -> throwError "Var not a variable binding"
      Just (VarBind a) -> pure a

data Typ =
    TyFn Typ Typ
    | TyBool
    | TyString
    | TyInt
    | TyPair Typ Typ
    | TyProduct [(Text, Typ)]
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
    | TmStr String
    | TmInt Int
    | TmPair Term Term
    | TmMkProd [(Text, Term)]
    | TmProjProd Text Term
    | TmProjUpdate Text Term Term

data TypeLevel = TypeLevel
  { context :: Context
  } deriving (Show)

type TypeChecker = ExceptT Text (ReaderT TypeLevel Identity)

class WithContext m where
  addBinding :: Var -> Binding -> m a -> m a
  askContext :: m Context

instance WithContext TypeChecker where
  addBinding v b k = do
    ctx <- reader context
    local (\tl -> tl { context = ((v, b) : ctx) }) k
  askContext = reader context

typeOf :: (WithContext m, MonadError Text m) => Term -> m Typ
typeOf (TmVar _ idx) =  getTypeFromContext idx
typeOf (TmLambda var a term) =
    addBinding var (VarBind a) $
      TyFn a <$> typeOf term
typeOf (TmApp f x) = do
    fnTyp <- typeOf f
    argTyp <- typeOf x
    case fnTyp of
      TyFn fm to -> if fm == argTyp
                    then pure to
                    else throwError $ "Type mismatch: expected "
                                <> tshow fm <> " but got " <> tshow argTyp
      notFn -> throwError $ "Expected function type, but got " <> tshow notFn
typeOf TmTrue = pure TyBool
typeOf TmFalse = pure TyBool
typeOf (TmIf test true false) = do
    tyTest <- typeOf test
    if tyTest == TyBool
      then pure ()
      else throwError "Error in If: test must be a Boolean"
    tyTrue <- typeOf true
    tyFalse <- typeOf false
    if tyTrue == tyFalse
      then pure tyTrue
      else throwError $ "TypeError in If: branches must be the same type, but are "
                  <> tshow tyTrue <> " and " <> tshow tyFalse
typeOf (TmStr _) = pure TyString
typeOf (TmInt _) = pure TyInt
typeOf (TmPair l r) = TyPair <$> typeOf l <*> typeOf r
typeOf (TmMkProd fs) =
  TyProduct <$> traverse (sequence . fmap typeOf) fs
typeOf (TmProjProd field record) = do
  withField field record $ \_ fTyp -> pure fTyp
typeOf (TmProjUpdate field val record) = do
  withField field record $ \rTyp fTyp -> do
    vTyp <- typeOf val
    if vTyp == fTyp
      then pure rTyp -- immutable data structure update returns the original datastructure
      else throwError $ "type mismatch: expected " <> tshow fTyp <> " but got " <> tshow vTyp

withField :: (WithContext m, MonadError Text m) => Text -> Term -> (Typ -> Typ -> m Typ) -> m Typ
withField field record k = do
  rTyp <- typeOf record
  case rTyp of
    TyProduct fs ->
      case lookup field fs of
        Just t -> k (TyProduct fs) t
        Nothing -> throwError $ "field " <> field <> " not found in type " <> tshow rTyp
    _ -> throwError $ "Attempted to access " <> field <> " but " <> tshow rTyp <> " is not a product type"

safeIndex :: Int -> [a] -> Maybe a
safeIndex idx = listToMaybe . drop (idx - 1)

tshow :: Show a => a -> Text
tshow = T.pack . show
