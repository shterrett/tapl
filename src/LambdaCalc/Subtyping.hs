{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LambdaCalc.Subtyping where

import Control.Monad (foldM)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.Reader (ReaderT, local, ask, runReaderT)
import Control.Monad.State (StateT, gets, modify, evalStateT)
import Data.Foldable (for_)
import Data.Functor.Identity (Identity, runIdentity)
import Data.List (union)
import Data.Maybe (listToMaybe, fromMaybe, mapMaybe)
import Data.Text (Text)
import Data.List.NonEmpty (nonEmpty, NonEmpty((:|)))
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
    | TyTop
    deriving (Eq, Ord, Show)

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

subtypeOf ::
  Typ
  -> Typ
  -> Bool
subtypeOf s t
  | s == t = True
  | otherwise = case (s, t) of
    (TyPair s1 s2, TyPair t1 t2) -> subtypeOf s1 t1 && subtypeOf s2 t2
    -- Records: S is a subtype of T when all the fields in T exist in S
    -- And the associated fields of S are subtypes of the fields of T
    (TyProduct ss, TyProduct ts) ->
      all (\(tag, typ) -> fromMaybe False $ flip subtypeOf typ <$> lookup tag ss) ts
    -- Sums: S is a subtype of T when all the constructors of S exist in T
    -- And the associated fields of S are subtypes of the fields in T
    (TySum ss, TySum ts) ->
      all (\(tag, typ) -> fromMaybe False $ subtypeOf typ <$> lookup tag ts) ss
    -- Functions: F: X -> Y is a subtype of G: U -> V when U is a subtype of S
    -- and T is a subtype of V
    (TyFn x y, TyFn u v) -> subtypeOf u x && subtypeOf y v
    (_, TyTop) -> True
    _ -> False

-- | Finds the least-common-supertype of two types
-- Used to determine the return type of branching expressions
-- specifically if and match
-- Because assignment to records and sum constructors does not allow subtyping,
-- we require type equality when comparing fields
joinTypes ::
  Typ
  -> Typ
  -> Maybe Typ
joinTypes s t
  | s == t = Just s
  | otherwise = case (s, t) of
    (TyPair s1 s2, TyPair t1 t2) ->
      TyPair <$> joinTypes s1 t1 <*> joinTypes s2 t2
    -- The join of a product has the intersection of the fields; it is a
    -- supertype of both products. (overlapping constructors msut have the same
    -- type)
    (TyProduct ss, TyProduct ts) ->
      let
        commonFields = mapMaybe (\(field, typ) -> (field, typ,) <$> lookup field ts) ss
      in
        Just . TyProduct $ mapMaybe (\(field, ft1, ft2) -> (field,) <$> equal ft1 ft2) commonFields
    -- The join of a sum has the union of all the constructors: it is a
    -- supertype of both of the sums. (overlapping constructors must have the
    -- same type)
    (TySum ss, TySum ts) ->
      let
        commonFields = mapMaybe (\(field, typ) -> (typ,) <$> lookup field ts) ss
      in
        (TySum $ ss `union` ts)
          <$ traverse (uncurry equal) commonFields
    (TyFn sIn sOut, TyFn tIn tOut) ->
      -- supertype of a function has a subtype argument and supertype return type
      TyFn <$> meetTypes sIn tIn <*> joinTypes sOut tOut
    _ -> Nothing

-- | Finds the greatest-common-subtype of two types
-- Used for determining the argument type of a function supertype (which is
-- contravariant)
-- Because assignment to records and sum constructors does not allow subtyping,
-- we require type equality when comparing fields
meetTypes ::
  Typ
  -> Typ
  -> Maybe Typ
meetTypes s t
  | s == t = Just s
  | otherwise = case (s, t) of
    (TyPair s1 s2, TyPair t1 t2) ->
      TyPair <$> meetTypes s1 t1 <*> meetTypes s2 t2
    -- The meet of a product has all of the common fields: it's a subtype of
    -- both products. (overlapping fields must have the same type)
    (TyProduct ss, TyProduct ts) ->
      let
        commonFields = mapMaybe (\(field, typ) -> (typ,) <$> lookup field ts) ss
      in
        (TyProduct $ ss `union` ts)
          <$ traverse (uncurry equal) commonFields
    -- The meet of a sum has only the intersection of fields: it's a subtype of
    -- both sums. (overlapping constructors must have the same type)
    (TySum ss, TySum ts) ->
      let
        commonFields = mapMaybe (\(field, typ) -> (field, typ,) <$> lookup field ts) ss
      in
        Just . TySum $ mapMaybe (\(field, ft1, ft2) -> (field,) <$> equal ft1 ft2) commonFields
    (TyFn sIn sOut, TyFn tIn tOut) ->
      -- subtype of a function has a supertype argument and a subtype return type
      TyFn <$> joinTypes sIn tIn <*> meetTypes sOut tOut
    _ -> Nothing


equal :: (Eq a) => a -> a -> Maybe a
equal a b = if a == b then Just a else Nothing

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
      TyFn fm to -> if subtypeOf argTyp fm
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
    case joinTypes tyTrue tyFalse of
      Just t -> pure t
      Nothing -> throwError $ "TypeError in If: branches must be the same type, but are "
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
    bs <- traverse (uncurry branchTypes) branches
    let
      outTyp = nonEmpty (snd <$> bs) >>= \case
          (t :| ts) -> foldM joinTypes t ts
      inTyp = nonEmpty (fst <$> bs) >>= \case
          (t :| ts) -> foldM equal t ts
    case (,) <$> inTyp <*> outTyp of
      Just (target, out) ->
        if target == haveType
          then pure out
          else throwError $ "type mismatch: expected match statement for "
                            <> tshow haveType
                            <> " but got " <> tshow target
      Nothing -> throwError $ "All branches of a match statement should have the same type, "
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
