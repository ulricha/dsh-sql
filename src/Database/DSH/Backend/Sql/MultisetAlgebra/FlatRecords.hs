{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ParallelListComp    #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.FlatRecords
    ( flattenMAPlan
    ) where

import           Data.Tuple
import           Control.Arrow
import           Control.Monad.Reader
import           Control.Monad.Except
import qualified Data.DList                                    as D
import           Data.List.NonEmpty                            (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                            as N
import           Data.Semigroup
import qualified Data.IntMap                                   as IM
import qualified Data.Foldable                                 as F
import           Text.Printf
import qualified Text.PrettyPrint.ANSI.Leijen                  as P

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import qualified Database.DSH.Common.Lang                      as L

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag.Build                    as B
import qualified Database.Algebra.Rewrite.Properties           as P
import qualified Database.Algebra.Table.Lang                   as TA
import qualified Database.Algebra.Table.Construct              as C

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.MultisetAlgebra.Typing
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.Serialize

--------------------------------------------------------------------------------
-- Annotated Tuple Types

data AnnPType a = AnnTupleT (NonEmpty (AnnPType a))
                | AnnAtomT a
                deriving (Show)

instance Pretty a => Pretty (AnnPType a) where
    pretty (AnnAtomT a)    = P.braces (pretty a)
    pretty (AnnTupleT tys) = prettyTupTy $ map pretty $ N.toList tys

instance Functor AnnPType where
    fmap f (AnnTupleT ts) = AnnTupleT $ fmap (fmap f) ts
    fmap f (AnnAtomT a)   = AnnAtomT $ f a

instance Foldable AnnPType where
    foldMap inj (AnnAtomT a)   = inj a
    foldMap inj (AnnTupleT ts) = F.fold $ fmap (foldMap inj) ts

newtype ColLabel = ColLabel { getLabel :: D.DList Char }

instance Show ColLabel where
    show = collapseLabel

prefixLabel :: ColLabel
prefixLabel = ColLabel $ pure 'c'

atomLabel :: ColLabel
atomLabel = ColLabel $ pure 'x'

pairFstLabel :: ColLabel
pairFstLabel = ColLabel $ pure '1'

pairSndLabel :: ColLabel
pairSndLabel = ColLabel $ pure '2'

tupElemLabel :: Int -> ColLabel
tupElemLabel i = ColLabel $ D.fromList $ show i

instance Semigroup ColLabel where
  ColLabel n1 <> ColLabel n2 = ColLabel $ n1 <> pure '_' <> n2

collapseLabel :: ColLabel -> TA.Attr
collapseLabel = D.toList . getLabel . (prefixLabel <>)

collapseExpr :: ColLabel -> TA.Expr
collapseExpr = TA.ColE . collapseLabel

mapi :: (a -> Int -> b) -> NonEmpty a -> NonEmpty b
mapi f (x :| xs) = f x 1 :| zipWith f xs [2..]

--------------------------------------------------------------------------------
-- Translate scalar operators

type RowType = NonEmpty ColLabel

--------------------------------------------------------------------------------
-- Translate scalar operators

algTy :: ScalarType -> TA.ATy
algTy IntT     = C.intT
algTy DoubleT  = C.doubleT
algTy BoolT    = C.boolT
algTy StringT  = C.stringT
algTy UnitT    = C.intT
algTy DateT    = C.dateT
algTy DecimalT = C.decT

algVal :: L.ScalarVal -> TA.AVal
algVal (L.IntV i)     = C.int (fromIntegral i)
algVal (L.BoolV t)    = C.bool t
algVal L.UnitV        = C.int 0xdeadbeef
algVal (L.StringV s)  = C.string s
algVal (L.DoubleV d)  = C.double d
algVal (L.DateV d)    = C.date $ L.unDate d
algVal (L.DecimalV d) = C.dec d

binOp :: L.ScalarBinOp -> TA.Expr -> TA.Expr -> TA.Expr
binOp (L.SBNumOp L.Add)        = TA.BinAppE TA.Plus
binOp (L.SBNumOp L.Sub)        = TA.BinAppE TA.Minus
binOp (L.SBNumOp L.Div)        = TA.BinAppE TA.Div
binOp (L.SBNumOp L.Mul)        = TA.BinAppE TA.Times
binOp (L.SBNumOp L.Mod)        = TA.BinAppE TA.Modulo
binOp (L.SBRelOp L.Eq)         = TA.BinAppE TA.Eq
binOp (L.SBRelOp L.NEq)        = TA.BinAppE TA.NEq
binOp (L.SBRelOp L.Gt)         = TA.BinAppE TA.Gt
binOp (L.SBRelOp L.GtE)        = TA.BinAppE TA.GtE
binOp (L.SBRelOp L.Lt)         = TA.BinAppE TA.Lt
binOp (L.SBRelOp L.LtE)        = TA.BinAppE TA.LtE
binOp (L.SBBoolOp L.Conj)      = TA.BinAppE TA.And
binOp (L.SBBoolOp L.Disj)      = TA.BinAppE TA.Or
binOp (L.SBStringOp L.Like)    = TA.BinAppE TA.Like
binOp (L.SBStringOp L.ReMatch) = TA.BinAppE TA.SimilarTo
binOp (L.SBDateOp L.AddDays)   = flip $ TA.BinAppE TA.Plus
binOp (L.SBDateOp L.SubDays)   = flip $ TA.BinAppE TA.Minus
binOp (L.SBDateOp L.DiffDays)  = flip $ TA.BinAppE TA.Minus

unOp :: L.ScalarUnOp -> TA.Expr -> TA.Expr
unOp (L.SUBoolOp L.Not)             = TA.UnAppE TA.Not
unOp (L.SUCastOp L.CastDouble)      = TA.UnAppE (TA.Cast C.doubleT)
unOp (L.SUCastOp L.CastDecimal)     = TA.UnAppE (TA.Cast C.decT)
unOp (L.SUNumOp L.Sin)              = TA.UnAppE TA.Sin
unOp (L.SUNumOp L.Cos)              = TA.UnAppE TA.Cos
unOp (L.SUNumOp L.Tan)              = TA.UnAppE TA.Tan
unOp (L.SUNumOp L.ASin)             = TA.UnAppE TA.ASin
unOp (L.SUNumOp L.ACos)             = TA.UnAppE TA.ACos
unOp (L.SUNumOp L.ATan)             = TA.UnAppE TA.ATan
unOp (L.SUNumOp L.Sqrt)             = TA.UnAppE TA.Sqrt
unOp (L.SUNumOp L.Exp)              = TA.UnAppE TA.Exp
-- DSH uses the Haskell meaning of log, namely the natural logarithm.
unOp (L.SUNumOp L.Log)              = TA.UnAppE TA.Ln
unOp (L.SUTextOp (L.SubString f t)) = TA.UnAppE (TA.SubString f t)
unOp (L.SUDateOp L.DateDay)         = TA.UnAppE TA.DateDay
unOp (L.SUDateOp L.DateMonth)       = TA.UnAppE TA.DateMonth
unOp (L.SUDateOp L.DateYear)        = TA.UnAppE TA.DateYear

joinRel :: L.BinRelOp -> TA.JoinRel
joinRel L.Eq  = TA.EqJ
joinRel L.Gt  = TA.GtJ
joinRel L.GtE = TA.GeJ
joinRel L.Lt  = TA.LtJ
joinRel L.LtE = TA.LeJ
joinRel L.NEq = TA.NeJ

-- | Map aggregate functions to relational aggregates for the
-- groupjoin operator. For Count, we need the first key column of the
-- right input to account for the NULLs produced by the outer join.
-- aggrFunGroupJoin :: Int -> SL.AggrFun -> AggrType
-- aggrFunGroupJoin _ (SL.AggrSum _ e)         = Sum $ taExpr e
-- aggrFunGroupJoin _ (SL.AggrMin e)           = Min $ taExpr e
-- aggrFunGroupJoin _ (SL.AggrMax e)           = Max $ taExpr e
-- aggrFunGroupJoin _ (SL.AggrAvg e)           = Avg $ taExpr e
-- aggrFunGroupJoin _ (SL.AggrAll e)           = All $ taExpr e
-- aggrFunGroupJoin _ (SL.AggrAny e)           = Any $ taExpr e
-- aggrFunGroupJoin c SL.AggrCount             = Count $ ColE (kc c)
-- aggrFunGroupJoin _ (SL.AggrCountDistinct e) = CountDistinct $ taExpr e

aggrFunGJ :: MonadError String m => TA.Attr -> AnnPType TA.Expr -> AggrFun TExpr -> m TA.AggrType
aggrFunGJ _ inpTy (AggrSum _ e)         = TA.Sum <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrMin e)           = TA.Min <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrMax e)           = TA.Max <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrAvg e)           = TA.Avg <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrAll e)           = TA.All <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrAny e)           = TA.Any <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ _ inpTy (AggrCountDistinct e) = TA.CountDistinct <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFunGJ c _     AggrCount             = pure $ TA.Count $ TA.ColE c

requiresOuterJoin :: AggrFun TExpr -> Bool
requiresOuterJoin a = case a of
    AggrSum _ _         -> True
    AggrAny _           -> True
    AggrAll _           -> True
    AggrCount           -> True
    AggrCountDistinct _ -> True
    AggrMax _           -> False
    AggrMin _           -> False
    AggrAvg _           -> False

aggrFun :: MonadError String m => AnnPType TA.Expr -> AggrFun TExpr -> m TA.AggrType
aggrFun inpTy (AggrSum _ e)         = TA.Sum <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrMin e)           = TA.Min <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrMax e)           = TA.Max <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAvg e)           = TA.Avg <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAll e)           = TA.All <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAny e)           = TA.Any <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrCountDistinct e) = TA.CountDistinct <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun _     AggrCount             = pure TA.CountStar

-- | The default value for sums over empty lists for all possible
-- numeric input types.
sumDefault :: ScalarType -> (TA.ATy, TA.AVal)
sumDefault IntT     = (TA.AInt, C.int 0)
sumDefault DoubleT  = (TA.ADouble, C.double 0)
sumDefault DecimalT = (TA.ADec, C.dec 0)
sumDefault ty       = error $ printf "FlatRecords.sumDefault: %s not a numeric type" (pp ty)

aggrFunDefault :: AggrFun TExpr -> Maybe TA.AVal
aggrFunDefault (AggrSum t _)         = Just $ snd $ sumDefault t
aggrFunDefault (AggrAny _)           = Just $ C.bool False
aggrFunDefault (AggrAll _)           = Just $ C.bool True
aggrFunDefault (AggrMax _)           = Nothing
aggrFunDefault (AggrMin _)           = Nothing
aggrFunDefault (AggrAvg _)           = Nothing
aggrFunDefault AggrCount             = Nothing
aggrFunDefault (AggrCountDistinct _) = Nothing

--------------------------------------------------------------------------------
-- Derive flat row expressions and row types

-- | Derive the row type from a tuple payload type
rowTy :: PType -> RowType
rowTy (PTupleT tys) = sconcat $ mapi (\ty i -> rowTyPath (tupElemLabel i) ty) tys
rowTy (PScalarT _)  = pure atomLabel
rowTy PIndexT       = pure atomLabel

rowTyPath :: ColLabel -> PType -> RowType
rowTyPath labelPath (PTupleT tys) = sconcat $ mapi (\ty i -> rowTyPath (labelPath <> tupElemLabel i) ty) tys
rowTyPath labelPath (PScalarT _)  = pure $ labelPath <> atomLabel
rowTyPath labelPath PIndexT       = pure $ labelPath <> atomLabel

rowTy' :: PType -> NonEmpty (ColLabel, ScalarType)
rowTy' (PTupleT tys) = sconcat $ mapi (\ty i -> rowTyPath' (tupElemLabel i) ty) tys
rowTy' (PScalarT ty) = pure (atomLabel, ty)
rowTy' PIndexT       = pure (atomLabel, IntT)

rowTyPath' :: ColLabel -> PType -> NonEmpty (ColLabel, ScalarType)
rowTyPath' labelPath (PTupleT tys) = sconcat $ mapi (\ty i -> rowTyPath' (labelPath <> tupElemLabel i) ty) tys
rowTyPath' labelPath (PScalarT ty) = pure (labelPath <> atomLabel, ty)
rowTyPath' labelPath PIndexT       = pure (labelPath <> atomLabel, IntT)

-- | Derive the flat row expression from an annotated payload type
rowExpr :: AnnPType a -> NonEmpty (ColLabel, a)
rowExpr (AnnTupleT tys) = sconcat $ mapi (\ty i -> rowExprPath (tupElemLabel i) ty) tys
rowExpr (AnnAtomT f)    = pure (atomLabel, f)

rowExprPath :: ColLabel -> AnnPType a -> NonEmpty (ColLabel, a)
rowExprPath labelPath (AnnTupleT tys) = sconcat $ mapi (\ty i -> rowExprPath (labelPath <> tupElemLabel i) ty) tys
rowExprPath labelPath (AnnAtomT f)    = pure (labelPath <> atomLabel, f)

flatExpr :: MonadError String m => AnnPType TA.Expr -> m TA.Expr
flatExpr ty@(AnnTupleT _) = throwError $ printf "FlatRecords.flatExpr: not an atomic expression %s" (pp ty)
flatExpr (AnnAtomT f)     = pure f

--------------------------------------------------------------------------------
-- Translate Operator Arguments

seedTyAnn ::  PType -> AnnPType ColLabel
seedTyAnn (PTupleT tys) = AnnTupleT $ mapi (\ty i -> seedTyAnnPrefix (tupElemLabel i) ty) tys
seedTyAnn (PScalarT _)  = AnnAtomT atomLabel
seedTyAnn PIndexT       = AnnAtomT atomLabel

seedTyAnnPrefix :: ColLabel -> PType -> AnnPType ColLabel
seedTyAnnPrefix labelPath (PTupleT tys) = AnnTupleT $ mapi (\ty i -> seedTyAnnPrefix (labelPath <> tupElemLabel i) ty) tys
seedTyAnnPrefix labelPath (PScalarT _)  = AnnAtomT (labelPath <> atomLabel)
seedTyAnnPrefix labelPath PIndexT       = AnnAtomT (labelPath <> atomLabel)

tupElemTys :: MonadError String m => AnnPType a -> m (NonEmpty (AnnPType a))
tupElemTys (AnnTupleT tys) = pure tys
tupElemTys (AnnAtomT _)    = throwError "not an annotated tuple type"

pushIfTy :: MonadError String m => TA.Expr -> AnnPType TA.Expr -> AnnPType TA.Expr -> m (AnnPType TA.Expr)
pushIfTy f (AnnTupleT tys1) (AnnTupleT tys2) = AnnTupleT <$> sequenceA (N.zipWith (pushIfTy f) tys1 tys2)
pushIfTy f (AnnAtomT f1)    (AnnAtomT f2)    = pure $ AnnAtomT $ TA.TernaryAppE TA.If f f1 f2
pushIfTy _ _                _                = throwError "pushIfTy: type mismatch"

pushEqTyJoin :: MonadError String m => AnnPType TA.Expr -> AnnPType TA.Expr -> m (AnnPType (TA.Expr, TA.Expr, TA.JoinRel))
pushEqTyJoin (AnnTupleT tys1) (AnnTupleT tys2) = AnnTupleT <$> sequenceA (N.zipWith pushEqTyJoin tys1 tys2)
pushEqTyJoin (AnnAtomT f1)    (AnnAtomT f2)    = pure $ AnnAtomT (f1, f2, TA.EqJ)
pushEqTyJoin _                _                = throwError "pushEqTyJoin: type mismatch"

pushNEqTyJoin :: MonadError String m => AnnPType TA.Expr -> AnnPType TA.Expr -> m (AnnPType (TA.Expr, TA.Expr, TA.JoinRel))
pushNEqTyJoin (AnnTupleT tys1) (AnnTupleT tys2) = AnnTupleT <$> sequenceA (N.zipWith pushNEqTyJoin tys1 tys2)
pushNEqTyJoin (AnnAtomT f1)    (AnnAtomT f2)    = pure $ AnnAtomT (f1, f2, TA.EqJ)
pushNEqTyJoin _                _                = throwError "pushNEqTyJoin: type mismatch"

exprAnnTy :: (MonadError String m, MonadReader (Maybe (AnnPType TA.Expr)) m) => TExpr -> m (AnnPType TA.Expr)
-- FIXME implement equality on records
exprAnnTy (TBinApp op e1 e2) = do
    ty1 <- exprAnnTy e1
    ty2 <- exprAnnTy e2
    case (ty1, ty2) of
        (AnnAtomT f1, AnnAtomT f2) -> pure $ AnnAtomT (binOp op f1 f2)
        _                          -> error "FIXME"
exprAnnTy (TUnApp op e)      = do
    ty <- exprAnnTy e
    case ty of
        AnnAtomT f -> pure $ AnnAtomT (unOp op f)
        _          -> error "FIXME"
exprAnnTy TInput             = do
    mTy <- ask
    case mTy of
        Just ty -> pure ty
        Nothing -> throwError "exprAnnTy: non-constant expression without input type"
exprAnnTy (TTupElem i e)     = do
    eTys <- exprAnnTy e >>= tupElemTys
    case safeIndexN i eTys of
        Just ty -> pure ty
        Nothing -> throwError "exprAnnTy: tuple element index out of bounds"
exprAnnTy (TMkTuple es)      = do
    eTys <- mapM exprAnnTy es
    pure $ AnnTupleT eTys
exprAnnTy (TConstant v)      = pure $ AnnAtomT $ TA.ConstE $ algVal v
exprAnnTy (TIf e1 e2 e3)     = do
    condTy <- exprAnnTy e1
    case condTy of
        AnnAtomT fcond -> do
            thenTy <- exprAnnTy e2
            elseTy <- exprAnnTy e3
            pushIfTy fcond thenTy elseTy
        _           -> throwError "exprAnnTy: if cond not scalar"
exprAnnTy TIndex             = pure $ AnnAtomT $ TA.ConstE $ TA.VInt 0xdeadbeef

inferExprAnnTy :: MonadError String m => (AnnPType TA.Expr) -> TExpr -> m (AnnPType TA.Expr)
inferExprAnnTy annInpTy e = runReaderT (exprAnnTy e) (Just annInpTy)

inferExprAnnTyConst :: MonadError String m => TExpr -> m (AnnPType TA.Expr)
inferExprAnnTyConst e = runReaderT (exprAnnTy e) Nothing

--------------------------------------------------------------------------------
-- Translate Operators

renameProj :: ColLabel -> RowType -> NonEmpty (TA.Attr, TA.Expr)
renameProj prefix attrs = fmap renameAttr attrs
  where
    renameAttr a = labelMapProj (prefix <> a) a

labelMapProj :: ColLabel -> ColLabel -> (TA.Attr, TA.Expr)
labelMapProj l1 l2 = (collapseLabel l1, TA.ColE $ collapseLabel l2)

opTy :: (MonadReader (NodeMap PType) m, MonadError String m) => AlgNode -> m PType
opTy n = do
    tyMap <- ask
    case IM.lookup n tyMap of
        Just ty -> pure ty
        Nothing -> throwError "FlattenRecords.opTy: no type binding for node"

flattenedNode :: AlgNode -> NodeMap AlgNode -> Flatten AlgNode
flattenedNode n m =
    case IM.lookup n m of
        Just n' -> pure n'
        Nothing -> throwError "FlatRecords.flattenedNode"

flattenUnOp :: PType -> AlgNode -> UnOp -> Flatten AlgNode
flattenUnOp inpTy taChild (Project e) = do
    let annTy = collapseExpr <$> seedTyAnn inpTy
    r <- fmap (first collapseLabel) <$> rowExpr <$> inferExprAnnTy annTy e
    C.proj (N.toList r) taChild
flattenUnOp inpTy taChild (Select e) = do
    let annTy = collapseExpr <$> seedTyAnn inpTy
    f <- inferExprAnnTy annTy e >>= flatExpr
    C.select f taChild
flattenUnOp _     taChild (Distinct ()) = do
    C.distinct taChild
flattenUnOp inpTy taChild (GroupAggr (groupExpr, aggrFuns)) = do
    let annTy = collapseExpr <$> seedTyAnn inpTy
    groupRow <- rowExpr <$> inferExprAnnTy annTy groupExpr
    let taGroupRow = fmap (first (collapseLabel . (pairFstLabel <>))) groupRow
    taAggrFuns <- sequenceA $ fmap (aggrFun annTy) $ L.getNE aggrFuns
    let taAggrProj = case taAggrFuns of
            a :| [] -> pure (atomLabel, a)
            as      -> mapi (\a i -> (tupElemLabel i <> atomLabel, a)) as
    let taAggrRow = fmap (swap . first (collapseLabel . (pairSndLabel <>))) taAggrProj
    C.aggr (N.toList taAggrRow) (N.toList taGroupRow) taChild
flattenUnOp inpTy taChild (RowNumPart (partExpr, sortExpr)) = do
    let annTy = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy
    flatPartExprs <- N.toList <$> fmap snd <$> rowExpr <$> inferExprAnnTy annTy partExpr
    flatSortExprs <- rowExpr <$> inferExprAnnTy annTy sortExpr
    let resCol = collapseLabel $ pairSndLabel <> atomLabel
        flatSortSpec = N.toList $ fmap (\(_, f) -> (f, TA.Asc)) flatSortExprs
    projNode <- insertRenameProj pairFstLabel inpTy taChild
    C.rownum' resCol flatSortSpec flatPartExprs projNode

insertRenameProj :: ColLabel -> PType -> AlgNode -> Flatten AlgNode
insertRenameProj prefix inpTy taChild = do
    let proj = N.toList $ renameProj prefix $ rowTy inpTy
    C.proj proj taChild

flattenJoinPred :: MonadError String m
                => AnnPType TA.Expr
                -> AnnPType TA.Expr
                -> L.JoinPredicate TExpr
                -> m [(TA.Expr, TA.Expr, TA.JoinRel)]
flattenJoinPred inpTy1 inpTy2 (L.JoinPred conjs) =
    N.toList <$> sconcat <$> (sequenceA $ fmap (flattenConjunct inpTy1 inpTy2) conjs)

flattenConjunct :: MonadError String m
                => AnnPType TA.Expr
                -> AnnPType TA.Expr
                -> L.JoinConjunct TExpr
                -> m (NonEmpty (TA.Expr, TA.Expr, TA.JoinRel))
flattenConjunct inpTy1 inpTy2 (L.JoinConjunct e1 L.Eq e2) = do
    e1'   <- inferExprAnnTy inpTy1 e1
    e2'   <- inferExprAnnTy inpTy2 e2
    fmap snd <$> rowExpr <$> pushEqTyJoin e1' e2'
flattenConjunct inpTy1 inpTy2 (L.JoinConjunct e1 L.NEq e2) = do
    e1'   <- inferExprAnnTy inpTy1 e1
    e2'   <- inferExprAnnTy inpTy2 e2
    fmap snd <$> rowExpr <$> pushNEqTyJoin e1' e2'
flattenConjunct inpTy1 inpTy2 (L.JoinConjunct e1 op e2)    = do
    e1' <- inferExprAnnTy inpTy1 e1 >>= flatExpr
    e2' <- inferExprAnnTy inpTy2 e2 >>= flatExpr
    pure $ pure (e1', e2', joinRel op)

flattenBinOp :: PType -> PType -> AlgNode -> AlgNode -> BinOp -> Flatten AlgNode
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 CartProduct{} = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    C.cross projNode1 projNode2
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (ThetaJoin p) = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    let annTy1 = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = collapseExpr <$> seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 p
    C.thetaJoin taPred projNode1 projNode2
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (SemiJoin p) = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    let annTy1 = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = collapseExpr <$> seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 p
    let leftRowTy = N.toList $ rowTy inpTy1
    let backProj = zipWith labelMapProj leftRowTy (map (pairFstLabel <>) leftRowTy)
    joinNode  <- C.semiJoin taPred projNode1 projNode2
    C.proj backProj joinNode
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (AntiJoin p) = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    let annTy1 = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = collapseExpr <$> seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 p
    let leftRowTy = N.toList $ rowTy inpTy1
    let backProj = zipWith labelMapProj leftRowTy (map (pairFstLabel <>) leftRowTy)
    joinNode  <- C.antiJoin taPred projNode1 projNode2
    C.proj backProj joinNode
flattenBinOp _      _     taChild1 taChild2 (Union ()) = do
    C.union taChild1 taChild2
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (LeftOuterJoin (joinPred,defaultVal,rightProj)) = do
    -- Prepare the TA join by simulating pair construction
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    let annTy1 = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = collapseExpr <$> seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 joinPred
    joinNode <- C.leftOuterJoin taPred projNode1 projNode2

    -- Columns from the left input
    let leftCols = map (collapseLabel . (pairFstLabel <>)) $ N.toList $ rowTy inpTy1
        leftProj = map (\c -> (c, TA.ColE c)) leftCols

    -- Columns from the right input: use coalesce to replace NULL columns with
    -- the default value.
    defaultColExprs <- rowExpr <$> inferExprAnnTyConst defaultVal
    rightColExprs   <- rowExpr <$> inferExprAnnTy annTy2 rightProj
    let coalProj = [ (collapseLabel $ pairSndLabel <> l, TA.BinAppE TA.Coalesce e de)
                   | (l, e)  <- rightColExprs
                   | (_, de) <- defaultColExprs
                   ]
    C.proj (leftProj ++ N.toList coalProj) joinNode
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (GroupJoin (p, as)) = do
    -- Prepare the TA join by simulating pair construction
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairSndLabel inpTy2 taChild2
    let annTy1 = collapseExpr <$> seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = collapseExpr <$> seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 p
    joinNode <- C.leftOuterJoin taPred projNode1 projNode2

    -- Group by all left input columns (superkey)
    let grpRow = N.toList $ fmap (\(l,e) -> (collapseLabel $ pairFstLabel <> l, e)) $ rowExpr annTy1

    -- Evaluate all aggregate functions on combined left and right columns
    let rightCol = collapseLabel $ pairSndLabel <> (N.head $ rowTy inpTy2)
    taAggrFuns <- mapM (aggrFunGJ rightCol (AnnTupleT (annTy1 :| [annTy2]))) (N.toList $ L.getNE as)
    let taAggrProj = case taAggrFuns of
            taAgg : [] -> pure (atomLabel, taAgg)
            taAggs     -> zipWith (\a i -> (tupElemLabel i <> atomLabel, a)) taAggs [1..]
    let taAggrRow = fmap (swap . first (collapseLabel . (pairSndLabel <>))) taAggrProj
    aggrNode <- C.aggr taAggrRow grpRow joinNode

    -- Provide the default value for aggregates that support it.
    let defaultVals = zip (map snd taAggrRow) (map aggrFunDefault (N.toList $ L.getNE as))
    let defaultRow = [ case mVal of
                            Just val -> (col, (TA.BinAppE TA.Coalesce (TA.ColE col) (TA.ConstE val)))
                            Nothing  -> (col, TA.ColE col)
                     | (col, mVal) <- defaultVals
                     ]
    C.proj (grpRow ++ defaultRow) aggrNode

--------------------------------------------------------------------------------
-- Provide information for base tables

baseTableColumns :: L.BaseTableSchema -> NonEmpty (TA.Attr, TA.ATy)
baseTableColumns schema = [ (c, algTy t)
                          | (L.ColName c, t) <- L.tableCols schema
                          ]

baseTableKeys :: L.BaseTableSchema -> [TA.Key]
baseTableKeys schema = [ TA.Key [ c | L.ColName c <- N.toList k ]
                       | L.Key k <- N.toList $ L.tableKeys schema
                       ]

--------------------------------------------------------------------------------
-- Translate literal lists

constTableExpr :: MonadError String m => TA.Expr -> m TA.AVal
constTableExpr (TA.ConstE v) = pure v
constTableExpr _             = throwError "constTableExpr: non-constant TA expression"

litRow :: MonadError String m => TExpr -> m [TA.AVal]
litRow e = do
    taExprs <- N.toList <$> fmap snd <$> rowExpr <$> inferExprAnnTyConst e
    sequenceA $ fmap constTableExpr taExprs

--------------------------------------------------------------------------------

flattenNullOp :: NullaryOp -> Flatten AlgNode
flattenNullOp (Lit (ty, es))          = do
    rows <- sequenceA $ fmap litRow es
    let schema = fmap (\(c, colTy) -> (collapseLabel c, algTy colTy)) $ rowTy' ty
    C.litTable' (F.toList rows) (N.toList schema)
flattenNullOp (Table (t, _, schema)) = do
    let cs = baseTableColumns schema
        ks = baseTableKeys schema
    tableNode <- C.dbTable t (N.toList cs) ks
    let p = mapi (\(c,_) i -> (collapseLabel $ tupElemLabel i <> atomLabel, TA.ColE c)) cs
    C.proj (N.toList p) tableNode

type Flatten = ReaderT (NodeMap PType) (B.BuildT TA.TableAlgebra (Except String))

flattenOp :: NodeMap MA -> MA -> AlgNode -> NodeMap AlgNode -> Flatten AlgNode
flattenOp _ TerOp{} _ _ = error "flattenOp: no ternary operators in MA"
flattenOp _ (UnOp o c) _ opMap      = do
    childTy <- opTy c
    taChild <- flattenedNode c opMap
    flattenUnOp childTy taChild o
flattenOp _ (BinOp o c1 c2) _ opMap = do
    childTy1 <- opTy c1
    childTy2 <- opTy c2
    taChild1 <- flattenedNode c1 opMap
    taChild2 <- flattenedNode c2 opMap
    flattenBinOp childTy1 childTy2 taChild1 taChild2 o
flattenOp _     (NullaryOp o) _ _   = do
    flattenNullOp o

lookupTANode :: MonadError String m => NodeMap AlgNode -> AlgNode -> m AlgNode
lookupTANode m n =
    case IM.lookup n m of
        Just n' -> pure n'
        Nothing -> throwError $ "lookupTANode: no mapping for " ++ (show n)

inferFlatDag :: NodeMap PType
             -> AlgebraDag MA
             -> B.BuildT TA.TableAlgebra (Except String) (NodeMap AlgNode)
inferFlatDag maTypes maDag = runReaderT (P.inferBottomUpE flattenOp maDag) maTypes

-- | Derive the relational representation of a vector type
vecScheme :: MonadError String m => PType -> AlgNode -> m TADVec
vecScheme ty n =
    case collapseLabel <$> seedTyAnn ty of
        AnnTupleT (sTy :| [kTy, oTy, pTy]) ->
            let s = VecRef $ F.foldMap pure sTy
                k = VecKey $ F.foldMap pure kTy
                o = VecOrder $ map (,TA.Asc) $ F.foldMap pure oTy
                p = VecItems $ F.foldMap pure pTy
            in pure $ TADVec n o k s p
        _                                  -> throwError "vecScheme: not a valid vector type"

toTADVec :: MonadError String m => NodeMap AlgNode -> NodeMap PType -> MADVec -> m TADVec
toTADVec nMap tyMap (MADVec n) = do
    n'   <- lookupTANode nMap n
    maTy <- runReaderT (opTy n) (tyMap)
    vecScheme maTy n'

inferFlatPlan :: QueryPlan MA MADVec
              -> B.BuildT TA.TableAlgebra (Except String) (Shape TADVec)
inferFlatPlan maPlan = do
    tyMap           <- inferMATypes $ queryDag maPlan
    nMap     <- inferFlatDag tyMap (queryDag maPlan)
    taShape  <- traverse (toTADVec nMap tyMap) (queryShape maPlan)
    serShape <- insertSerialize taShape
    pure serShape

flattenMAPlan :: QueryPlan MA MADVec -> QueryPlan TA.TableAlgebra TADVec
flattenMAPlan plan =
    case runExcept $ B.runBuildT (inferFlatPlan plan) of
        Left msg                             ->
            error $ "flattenMAPlan: " ++ msg
        Right (taDag, taShape, _) ->
            QueryPlan { queryDag   = addRootNodes taDag (shapeNodes taShape)
                      , queryShape = taShape
                      , queryTags  = IM.empty
                      }
