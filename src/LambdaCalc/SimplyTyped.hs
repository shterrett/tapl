{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LambdaCalc.SimplyTyped where

import Control.Monad (foldM)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.Reader (ReaderT, local, ask, runReaderT)
import Control.Monad.State (StateT, gets, modify, evalStateT)
import Data.Foldable (for_)
import Data.Functor.Identity (Identity, runIdentity)
import Data.List (nub)
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
    | TyUnit
    | TyPair Typ Typ
    | TyProduct [(Text, Typ)]
    | TySum [(Text, Typ)]
  -- ^ The list of all the variants of the sum type, with the
  -- (single) type that it may contain
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
    | TmUnit
    | TmPair Term Term
    | TmMkProd [(Text, Term)]
    | TmProjProd Text Term
    | TmUpdateProd Text Term Term
    | TmDeclareSum [(Text, Typ)]
    | TmCall Text Term
    -- ^ Right now, used for sum type injection. However, can be used for named
    -- functions with declared types later
    | TmMatchSum Term [(Text, Term)]
    | TmSequence [Term]

newtype TypeEnv = TypeEnv { getTypeEnv :: [(Text, Typ)] }
  deriving (Show)

type TypeChecker = ExceptT Text (StateT TypeEnv (ReaderT Context Identity))

class WithContext m where
  addBinding :: Var -> Binding -> m a -> m a
  askContext :: m Context

instance WithContext TypeChecker where
  addBinding v b k =
    local ((v, b) :) k
  askContext = ask

class (MonadError Text m) => WithTypeEnv m where
  lookupType :: Text -> m Typ
  addType :: Text -> Typ -> m ()

instance WithTypeEnv TypeChecker where
  lookupType name = do
    env <- gets getTypeEnv
    case lookup name env of
      Just t -> pure t
      Nothing -> throwError $ "type name " <> name <> " not found"
  addType name typ = modify $ TypeEnv . ((name, typ) :) . getTypeEnv

typeOf ::
  forall m.
  ( WithContext m
  , WithTypeEnv m
  , MonadError Text m
  )
  => Term
  -> m Typ
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
typeOf TmUnit = pure TyUnit
typeOf (TmPair l r) = TyPair <$> typeOf l <*> typeOf r
typeOf (TmMkProd fs) =
    TyProduct <$> traverse (sequence . fmap typeOf) fs
typeOf (TmProjProd field record) = do
    withField field record $ \_ fTyp -> pure fTyp
typeOf (TmUpdateProd field val record) = do
    withField field record $ \rTyp fTyp -> do
      vTyp <- typeOf val
      if vTyp == fTyp
        then pure rTyp -- immutable data structure update returns the original datastructure
        else throwError $ "type mismatch: expected " <> tshow fTyp <> " but got " <> tshow vTyp
typeOf (TmDeclareSum variants) = for_ variants bindSumType >> pure TyUnit
  where bindSumType (name, typ) = addType name $ TyFn typ (TySum variants)
typeOf (TmCall fn arg) = do
    fnTyp <- lookupType fn
    haveTyp <- typeOf arg
    case fnTyp of
      TyFn wantTyp returnTyp ->
        if haveTyp == wantTyp
          then pure returnTyp
          else throwError $ "type mismatch: expected " <> tshow wantTyp
                          <> "but got " <> tshow haveTyp
                          <> "when calling " <> fn
      _ -> throwError $ "type mismatch: attempted to call " <> fn
                        <> " but it is not a function"
typeOf (TmMatchSum term branches) = do
    haveType <- typeOf term
    case haveType of
      TySum _ -> pure ()
      _ -> throwError $ "Match statements are only valid with sum types. "
                        <> tshow haveType <> " was provided"
    bs <- nub <$> traverse (uncurry branchTypes) branches
    case bs of
      [(target, out)] ->
        if target == haveType
          then pure out
          else throwError $ "type mismatch: expected match statement for "
                            <> tshow haveType
                            <> " but got " <> tshow target
      _ -> throwError $ "All branches of a match statement should have the same type, "
                        <> "but the following types were found "
                        <> tshow (snd <$> bs)
    where
      branchTypes ::
        Text -- ^ name of the constructor
        -> Term -- ^ the body of the match arm
        -> m (Typ, Typ) -- ^ ( input (sum) type
                        --   , output type)
      branchTypes name body = do
        variant <- lookupType name
        result <- typeOf body
        case variant of
          TyFn input s@(TySum _) ->
            case result of
              TyFn input' output ->
                if input == input'
                  then pure (s, output)
                  else throwError $ "type mismatch: expected match arm to take "
                                    <> tshow input <> " but actually takes " <> tshow input'
              armErr ->
                throwError $ "match arm should be function from a variant of the sum type; instead is "
                            <> tshow armErr
          _ -> throwError $ "match arm should be a constructor of a sum type "
                            <> "instead got " <> tshow variant
typeOf (TmSequence ts) = foldM (const typeOf) TyUnit ts

withField ::
  ( WithContext m
  , WithTypeEnv m
  , MonadError Text m
  )
  => Text
  -> Term
  -> (Typ -> Typ -> m Typ)
  -> m Typ
withField field record k = do
  rTyp <- typeOf record
  case rTyp of
    TyProduct fs ->
      case lookup field fs of
        Just t -> k (TyProduct fs) t
        Nothing -> throwError $ "field " <> field <> " not found in type " <> tshow rTyp
    _ -> throwError $ "Attempted to access " <> field <> " but " <> tshow rTyp <> " is not a product type"

typecheck :: Term -> Either Text Typ
typecheck =
  runIdentity
  . flip runReaderT []
  . flip evalStateT (TypeEnv [])
  . runExceptT
  . (typeOf @TypeChecker)

safeIndex :: Int -> [a] -> Maybe a
safeIndex idx = listToMaybe . drop (idx - 1)

tshow :: Show a => a -> Text
tshow = T.pack . show
