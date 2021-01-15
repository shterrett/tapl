{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SystemF.TypeChecker where

import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.Reader (ReaderT, local, ask, runReaderT)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T

data Typ =
  TyFn Typ Typ
    | TyVar DeBruijn -- total depth; distance to binder
    | TyAll Text Typ -- variable name
    | TySome Text Typ -- variable name
    | TyBool
    deriving (Eq, Show)

data Binding =
  NameBind
    | VarBind Typ
    | TyVarBind

type Var = Text
type Context = [(Var, Binding)]

newtype DeBruijn = DeBruijn { unDeBruijn :: Int }
                   deriving newtype (Show, Eq)

getTypeFromContext :: (WithContext m, MonadError Text m) => DeBruijn -> m Typ
getTypeFromContext (DeBruijn idx) = do
    ctx <- askContext
    case bindingShift (idx + 1) . snd <$> safeIndex idx ctx of
      Nothing -> throwError "Var not found"
      Just NameBind -> throwError "Var not a variable binding"
      Just TyVarBind -> throwError "Var not a variable binding"
      Just (VarBind a) -> pure a

bindingShift :: Int -> Binding -> Binding
bindingShift offset = \case
  VarBind a -> VarBind $ typeShift offset a
  a -> a

type TypeChecker = ExceptT Text (ReaderT Context Identity)

class WithContext m where
  addBinding :: Var -> Binding -> m a -> m a
  askContext :: m Context

instance WithContext TypeChecker where
  addBinding v b k =
    local ((v, b) :) k
  askContext = ask

tymap :: (Int -> DeBruijn -> Typ) -> Int -> Typ -> Typ
tymap onvar cut tyT = walk cut tyT
  where
    walk :: Int -> Typ -> Typ
    walk c (TyFn fm to) = TyFn (walk c fm) (walk c to)
    walk c (TyVar debruijn) = onvar c debruijn
    walk c (TyAll name typ) = TyAll name $ walk (succ c) typ
    walk c (TySome name typ) = TySome name $ walk (succ c) typ
    walk _ TyBool = TyBool

typeShiftAbove :: Int -> Int -> Typ -> Typ
typeShiftAbove depth =
  tymap (\c (DeBruijn x) -> if x >= c
                              then TyVar (DeBruijn $ x + depth)
                              else TyVar (DeBruijn x)
        )

typeShift :: Int -> Typ -> Typ
typeShift depth = typeShiftAbove depth 0

typeSubst :: Typ -> Int -> Typ -> Typ
typeSubst sub var typ =
  tymap (\j (DeBruijn x) -> if x == j
                              then (typeShift j sub)
                              else (TyVar $ DeBruijn x)
        )
        var
        typ

typeSubstTop :: Typ -> Typ -> Typ
typeSubstTop sub typ = typeShift (-1) $ typeSubst (typeShift 1 sub) 0 typ

data Term =
    TmVar DeBruijn
    | TmLambda Text Typ Term
    | TmApp Term Term
  -- Universal types
    | TmTAbs Text Term
    | TmTApp Term Typ
  -- Existential types
    | TmPack Typ Term Typ -- forall inside the parens to the left of an arrow
                          -- (real type) (dictionary using real type) (existential type)
    | TmUnpack Text Text Term Term
    | TmTrue
    | TmFalse

-- packing
-- {*Int, 4} as x
-- {*Int, (+)} as {existsX, (x -> x -> x)}
-- {*Nat, {a=5 : Nat, f=\x:Nat. succ x}} as {existsX, {a:X, f:X -> Nat}};
-- {*String, {a="Hello" : String, f=\x:String. length x}} as {existsX, {a:X, f:X -> Nat}};
-- unpacking
-- let {Foo, x} = tm in (id @Foo x) :: Foo

typeOf ::
  forall m.
  ( WithContext m
  , MonadError Text m
  )
  => Term
  -> m Typ
typeOf (TmVar idx) =  getTypeFromContext idx
typeOf (TmLambda var a term) =
    addBinding var (VarBind a) $ do
      termType <- typeShift (-1) <$> typeOf term
      pure $ TyFn a termType
typeOf (TmApp f x) = do
    fnTyp <- typeOf f
    argTyp <- typeOf x
    case fnTyp of
      TyFn fm to -> if fm == argTyp
                    then pure to
                    else throwError $ "Type mismatch: expected "
                                <> tshow fm <> " but got " <> tshow argTyp
      notFn -> throwError $ "Expected function type, but got " <> tshow notFn
typeOf (TmTAbs typeName term) = do
  addBinding typeName TyVarBind $
    TyAll typeName <$> typeOf term
typeOf (TmTApp term typ) = do
  termTyp <- typeOf term
  case termTyp of
    TyAll _ forallTyp -> pure $ typeSubstTop typ forallTyp
    e -> throwError $ "Type mismatch: expected forall but got " <> tshow e
typeOf (TmPack innerTyp term overType) = do
  case overType of
    TySome _ someType -> do
      termType <- typeOf term
      let termType' = typeSubstTop innerTyp someType
      if termType == termType'
        then pure overType
        else throwError $ tshow termType <> "doesn't match declared type" <> tshow innerTyp
    e -> throwError $ "expected existential, but got " <> tshow e
typeOf (TmUnpack typeName varName bind body) = do
  bindType <- typeOf bind
  case bindType of
    TySome _ someType -> do
      addBinding typeName TyVarBind $ do
        addBinding varName (VarBind someType) $ do
          typeShift (-2) <$> typeOf body
    e -> throwError $ "expected existential, but got " <> tshow e
typeOf TmTrue = pure TyBool
typeOf TmFalse = pure TyBool

safeIndex :: Int -> [a] -> Maybe a
safeIndex idx = listToMaybe . drop (idx - 1)

tshow :: Show a => a -> Text
tshow = T.pack . show

typecheck :: Term -> Either Text Typ
typecheck =
  runIdentity
  . flip runReaderT []
  . runExceptT
  . (typeOf @TypeChecker)
