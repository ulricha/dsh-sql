{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.Typing
    ( tyUnOp
    , tyBinOp
    , tyNullOp
    ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Data.List
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))
import           Text.Printf
import           Data.List.NonEmpty(NonEmpty((:|)))

import qualified Database.DSH.Common.Lang as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import qualified Database.DSH.Common.VectorLang as VL

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang

type Infer = ExceptT String Identity

tyErr :: (MonadError String m, Pretty o) => String -> o -> [VL.PType] -> m a
tyErr op arg csTys = throwError $ printf "%s{%s} %s" op (pp arg) (concat $ intersperse " " (map pp csTys))

pPairT :: VL.PType -> VL.PType -> VL.PType
pPairT ty1 ty2 = VL.PTupleT $ ty1 :| pure ty2

expTy :: VL.PType -> VL.TExpr -> Infer VL.PType
expTy ty e = runReaderT (VL.tExpTy e) (Just ty)

constEnvTy :: VL.TExpr -> Infer VL.PType
constEnvTy e = runReaderT (VL.tExpTy e) Nothing

aggrTy :: VL.PType -> VL.AggrFun VL.TExpr -> Infer VL.PType
aggrTy ty a = runReaderT (VL.tAggrTy a) (Just ty)

-- | Typing of unary MA operators
tyUnOp :: VL.PType -> UnOp -> Infer VL.PType
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
tyBinOp :: VL.PType -> VL.PType -> BinOp -> Infer VL.PType
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
tyNullOp :: NullaryOp -> Infer VL.PType
tyNullOp (Table (_, ty, _)) = pure ty
tyNullOp (Lit (ty, es))     = do
    eTys <- sequenceA $ fmap constEnvTy es
    if all (== ty) eTys
        then pure ty
        else tyErr "lit" (ty, es) []
