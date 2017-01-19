{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.FlatRecords
    ( flattenPlan
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

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang
import           Database.DSH.Common.Nat
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

--------------------------------------------------------------------------------
-- Annotated Tuple Types

data AnnPType = AnnTupleT (NonEmpty AnnPType)
              | AnnAtomT TA.Expr

newtype ColLabel = ColLabel { getLabel :: D.DList Char }

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
binOp (L.SBNumOp L.Add)       = TA.BinAppE TA.Plus
binOp (L.SBNumOp L.Sub)       = TA.BinAppE TA.Minus
binOp (L.SBNumOp L.Div)       = TA.BinAppE TA.Div
binOp (L.SBNumOp L.Mul)       = TA.BinAppE TA.Times
binOp (L.SBNumOp L.Mod)       = TA.BinAppE TA.Modulo
binOp (L.SBRelOp L.Eq)        = TA.BinAppE TA.Eq
binOp (L.SBRelOp L.NEq)       = TA.BinAppE TA.NEq
binOp (L.SBRelOp L.Gt)        = TA.BinAppE TA.Gt
binOp (L.SBRelOp L.GtE)       = TA.BinAppE TA.GtE
binOp (L.SBRelOp L.Lt)        = TA.BinAppE TA.Lt
binOp (L.SBRelOp L.LtE)       = TA.BinAppE TA.LtE
binOp (L.SBBoolOp L.Conj)     = TA.BinAppE TA.And
binOp (L.SBBoolOp L.Disj)     = TA.BinAppE TA.Or
binOp (L.SBStringOp L.Like)   = TA.BinAppE TA.Like
binOp (L.SBDateOp L.AddDays)  = flip $ TA.BinAppE TA.Plus
binOp (L.SBDateOp L.SubDays)  = flip $ TA.BinAppE TA.Minus
binOp (L.SBDateOp L.DiffDays) = flip $ TA.BinAppE TA.Minus

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

aggrFun :: MonadError String m => AnnPType -> AggrFun TExpr -> m TA.AggrType
aggrFun inpTy (AggrSum _ e)         = TA.Sum <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrMin e)           = TA.Min <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrMax e)           = TA.Max <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAvg e)           = TA.Avg <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAll e)           = TA.All <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrAny e)           = TA.Any <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun inpTy (AggrCountDistinct e) = TA.CountDistinct <$> (inferExprAnnTy inpTy e >>= flatExpr)
aggrFun _     AggrCount             = pure TA.CountStar

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
rowExpr :: AnnPType -> NonEmpty (ColLabel, TA.Expr)
rowExpr (AnnTupleT tys) = sconcat $ mapi (\ty i -> rowExprPath (tupElemLabel i) ty) tys
rowExpr (AnnAtomT f)    = pure (atomLabel, f)

rowExprPath :: ColLabel -> AnnPType -> NonEmpty (ColLabel, TA.Expr)
rowExprPath labelPath (AnnTupleT tys) = sconcat $ mapi (\ty i -> rowExprPath (labelPath <> tupElemLabel i) ty) tys
rowExprPath labelPath (AnnAtomT f)    = pure (labelPath <> atomLabel, f)

flatExpr :: MonadError String m => AnnPType -> m TA.Expr
flatExpr (AnnTupleT _) = throwError "FlatRecords.flatExpr: not an atomic expression"
flatExpr (AnnAtomT f)  = pure f

--------------------------------------------------------------------------------
-- Translate Operator Arguments

seedTyAnn ::  PType -> AnnPType
seedTyAnn (PTupleT tys) = AnnTupleT $ mapi (\ty i -> seedTyAnnPrefix (tupElemLabel i) ty) tys
seedTyAnn (PScalarT _)  = AnnAtomT (TA.ColE $ collapseLabel atomLabel)
seedTyAnn PIndexT       = AnnAtomT (TA.ColE $ collapseLabel atomLabel)

seedTyAnnPrefix :: ColLabel -> PType -> AnnPType
seedTyAnnPrefix labelPath (PTupleT tys) = AnnTupleT $ mapi (\ty i -> seedTyAnnPrefix (labelPath <> tupElemLabel i) ty) tys
seedTyAnnPrefix labelPath (PScalarT _)  = AnnAtomT (TA.ColE $ collapseLabel $ labelPath <> atomLabel)
seedTyAnnPrefix labelPath PIndexT       = AnnAtomT (TA.ColE $ collapseLabel $ labelPath <> atomLabel)

tupElemTys :: MonadError String m => AnnPType -> m (NonEmpty AnnPType)
tupElemTys (AnnTupleT tys) = pure tys
tupElemTys (AnnAtomT _)    = throwError "not an annotated tuple type"

pushIfTy :: MonadError String m => TA.Expr -> AnnPType -> AnnPType -> m AnnPType
pushIfTy f (AnnTupleT tys1) (AnnTupleT tys2) = AnnTupleT <$> sequenceA (N.zipWith (pushIfTy f) tys1 tys2)
pushIfTy f (AnnAtomT f1)    (AnnAtomT f2)    = pure $ AnnAtomT $ TA.TernaryAppE TA.If f f1 f2
pushIfTy _ _                _                = throwError "pushIfTy: type mismatch"

exprAnnTy :: (MonadError String m, MonadReader (Maybe AnnPType) m) => TExpr -> m AnnPType
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

inferExprAnnTy :: MonadError String m => AnnPType -> TExpr -> m AnnPType
inferExprAnnTy annInpTy e = runReaderT (exprAnnTy e) (Just annInpTy)

inferExprAnnTyConst :: MonadError String m => TExpr -> m AnnPType
inferExprAnnTyConst e = runReaderT (exprAnnTy e) Nothing

--------------------------------------------------------------------------------
-- Translate Operators

renameProj :: ColLabel -> RowType -> NonEmpty (TA.Attr, TA.Expr)
renameProj prefix attrs = fmap renameAttr attrs
  where
    renameAttr a = (collapseLabel $ prefix <> a, TA.ColE $ collapseLabel a)

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
    let annTy = seedTyAnn inpTy
    r <- fmap (first collapseLabel) <$> rowExpr <$> inferExprAnnTy annTy e
    C.proj (N.toList r) taChild
flattenUnOp inpTy taChild (Select e) = do
    let annTy = seedTyAnn inpTy
    f <- inferExprAnnTy annTy e >>= flatExpr
    C.select f taChild
flattenUnOp _     taChild (Distinct ()) = do
    C.distinct taChild
flattenUnOp inpTy taChild (GroupAggr (groupExpr, aggrFuns)) = do
    let annTy = seedTyAnn inpTy
    groupRow <- rowExpr <$> inferExprAnnTy annTy groupExpr
    let taGroupRow = fmap (first (collapseLabel . (pairFstLabel <>))) groupRow
    taAggrFuns <- sequenceA $ fmap (aggrFun annTy) $ L.getNE aggrFuns
    let taAggrProj = case taAggrFuns of
            a :| [] -> pure (atomLabel, a)
            as      -> mapi (\a i -> (tupElemLabel i <> atomLabel, a)) as
    let taAggrRow = fmap (swap . first (collapseLabel . (pairSndLabel <>))) taAggrProj
    C.aggr (N.toList taAggrRow) (N.toList taGroupRow) taChild
flattenUnOp inpTy taChild (RowNumPart (partExpr, sortExpr)) = do
    let annTy = seedTyAnnPrefix pairFstLabel inpTy
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
                => AnnPType
                -> AnnPType
                -> L.JoinPredicate TExpr
                -> m [(TA.Expr, TA.Expr, TA.JoinRel)]
flattenJoinPred inpTy1 inpTy2 (L.JoinPred conjs) =
    N.toList <$> sequenceA (fmap (flattenConjunct inpTy1 inpTy2) conjs)

flattenConjunct :: MonadError String m
                => AnnPType
                -> AnnPType
                -> L.JoinConjunct TExpr
                -> m (TA.Expr, TA.Expr, TA.JoinRel)
flattenConjunct inpTy1 inpTy2 (L.JoinConjunct e1 op e2) = do
    e1' <- inferExprAnnTy inpTy1 e1 >>= flatExpr
    e2' <- inferExprAnnTy inpTy2 e2 >>= flatExpr
    pure (e1', e2', joinRel op)

flattenBinOp :: PType -> PType -> AlgNode -> AlgNode -> BinOp -> Flatten AlgNode
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 CartProduct{} = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairFstLabel inpTy2 taChild2
    C.cross projNode1 projNode2
flattenBinOp inpTy1 inpTy2 taChild1 taChild2 (ThetaJoin p) = do
    projNode1 <- insertRenameProj pairFstLabel inpTy1 taChild1
    projNode2 <- insertRenameProj pairFstLabel inpTy2 taChild2
    let annTy1 = seedTyAnnPrefix pairFstLabel inpTy1
        annTy2 = seedTyAnnPrefix pairSndLabel inpTy2
    taPred    <- flattenJoinPred annTy1 annTy2 p
    C.thetaJoin taPred projNode1 projNode2

--------------------------------------------------------------------------------
-- Provide information for base tables

baseTableColumns :: L.BaseTableSchema -> [(TA.Attr, TA.ATy)]
baseTableColumns schema = [ (c, algTy t)
                          | (L.ColName c, t) <- N.toList $ L.tableCols schema
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
flattenNullOp (Table (t, _, schema)) = C.dbTable t cs ks
  where
    cs = baseTableColumns schema
    ks = baseTableKeys schema

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
flattenOp _     (NullaryOp o) _ _            = do
    flattenNullOp o

lookupTANode :: NodeMap AlgNode -> AlgNode -> Except String AlgNode
lookupTANode m n =
    case IM.lookup n m of
        Just n' -> pure n'
        Nothing -> throwError $ "lookupTANode: no mapping for " ++ (show n)

inferFlatPlan :: AlgebraDag MA -> Except String (AlgebraDag TA.TableAlgebra)
inferFlatPlan maPlan = do
    maTypes        <- inferMATypes maPlan
    (taDag, nm, _) <- B.runBuildT $ runReaderT (P.inferBottomUpE flattenOp maPlan) maTypes
    taRoots        <- mapM (lookupTANode nm) (rootNodes maPlan)
    pure $ addRootNodes taDag taRoots

flattenPlan :: AlgebraDag MA -> AlgebraDag TA.TableAlgebra
flattenPlan maPlan =
    case runExcept (inferFlatPlan maPlan) of
        Left msg     -> error msg
        Right taPlan -> taPlan
