{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.Typing
    ( inferMATypes
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.List
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))
import           Text.Printf
import           Data.List.NonEmpty(NonEmpty((:|)))
import qualified Data.IntMap                                   as IM

import           Database.Algebra.Dag.Common
import           Database.Algebra.Dag

import qualified Database.DSH.Common.Lang as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.Common.Opt
import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.VectorLang as VL

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang

--------------------------------------------------------------------------------
-- Typing Helpers

-- | Type errors for MA operators
tyErr :: (MonadError String m, Pretty o) => String -> o -> [VL.PType] -> m a
tyErr op arg csTys = throwError $ printf "%s{%s} %s" op (pp arg) (concat $ intersperse " " (map pp csTys))

pPairT :: VL.PType -> VL.PType -> VL.PType
pPairT ty1 ty2 = VL.PTupleT $ ty1 :| pure ty2

-- | Typecheck a tuple expression with the given input type
expTy :: MonadError String m => VL.PType -> VL.TExpr -> m VL.PType
expTy ty e = runReaderT (VL.tExpTy e) (Just ty)

-- | Typecheck a *constant* tuple expression
constEnvTy :: MonadError String m => VL.TExpr -> m VL.PType
constEnvTy e = runReaderT (VL.tExpTy e) Nothing

-- | Typecheck an aggregate function with the given input type
aggrTy :: MonadError String m => VL.PType -> VL.AggrFun VL.TExpr -> m VL.PType
aggrTy ty a = runReaderT (VL.tAggrTy a) (Just ty)

--------------------------------------------------------------------------------
-- Typing of operators

-- | Typing of unary MA operators
tyUnOp :: MonadError String m => VL.PType -> UnOp -> m VL.PType
tyUnOp ty (Project e) = expTy ty e
tyUnOp ty (Select e) = do
    predTy <- expTy ty e
    case predTy of
        VL.PScalarT BoolT -> pure ty
        _                 -> tyErr "select" e [ty]
tyUnOp ty (Distinct ()) = pure ty
tyUnOp ty (GroupAggr (e, (L.NE as))) = do
    gTy  <- expTy ty e
    aTys <- sequenceA $ fmap (aggrTy ty) as
    pure $ VL.PTupleT (gTy :| pure (VL.PTupleT aTys))
tyUnOp ty (RowNumPart (p, o)) = do
    _ <- expTy ty p
    _ <- expTy ty o
    pure $ VL.PTupleT (ty :| [VL.PScalarT IntT])

-- | Typing of binary MA operators
tyBinOp :: MonadError String m => VL.PType -> VL.PType -> BinOp -> m VL.PType
tyBinOp ty1 ty2 (CartProduct ())        = pure $ pPairT ty1 ty2
tyBinOp ty1 ty2 (ThetaJoin p)           = VL.predTy ty1 ty2 p >> pure (pPairT ty1 ty2)
tyBinOp ty1 ty2 (SemiJoin p)            = VL.predTy ty1 ty2 p >> pure ty1
tyBinOp ty1 ty2 (AntiJoin p)            = VL.predTy ty1 ty2 p >> pure ty1
tyBinOp ty1 ty2 (LeftOuterJoin (p,d,r)) = do
    VL.predTy ty1 ty2 p
    dTy <- constEnvTy d
    rTy <- expTy ty2 r
    if dTy == rTy
       then pure $ pPairT ty1 dTy
       else tyErr "leftouterjoin" (p,d,r) [ty1, ty2]
tyBinOp ty1 ty2 (GroupJoin (p, as))     = do
    VL.predTy ty1 ty2 p
    aTys <- sequenceA $ fmap (aggrTy (pPairT ty1 ty2)) $ L.getNE as
    pure $ pPairT ty1 (VL.PTupleT aTys)
tyBinOp ty1 ty2 (Union ())              = do
    if ty1 == ty2
       then pure ty1
       else tyErr "union" () [ty1, ty2]

-- | Typing of nullary operators
tyNullOp :: MonadError String m => NullaryOp -> m VL.PType
tyNullOp (Table (_, ty, _)) = pure ty
tyNullOp (Lit (ty, es))     = do
    eTys <- sequenceA $ fmap constEnvTy es
    if all (== ty) eTys
        then pure ty
        else tyErr "lit" (ty, es) []

--------------------------------------------------------------------------------
-- Typing of multiset algebra DAGs

-- | Infer a type for all operators in an MA Dag.
inferMATypes :: MonadError String m => AlgebraDag MA -> m (NodeMap VL.PType)
inferMATypes = inferBottomUpE tyOp

childTy :: MonadError String m => AlgNode -> NodeMap VL.PType -> m VL.PType
childTy n m =
    case IM.lookup n m of
        Just ty -> pure ty
        Nothing -> throwError $ printf "No type node %d" n

tyOp :: MonadError String m => NodeMap MA -> MA -> AlgNode -> NodeMap VL.PType -> m VL.PType
tyOp _ (BinOp o c1 c2) _ tyMap = do
    ty1 <- childTy c1 tyMap
    ty2 <- childTy c2 tyMap
    tyBinOp ty1 ty2 o
tyOp _ (UnOp o c) _ tyMap      = do
    ty <- childTy c tyMap
    tyUnOp ty o
tyOp _ (NullaryOp o) _ _       = tyNullOp o
tyOp _ TerOp{} _ _             = $impossible
