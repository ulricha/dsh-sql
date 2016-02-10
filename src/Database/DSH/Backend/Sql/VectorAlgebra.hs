{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- | Implementation of vector primitives in terms of table algebra
-- operators.
module Database.DSH.Backend.Sql.VectorAlgebra
    ( ic, kc, oc, rc
    ) where

import           Control.Exception.Base
import           Data.List                        (transpose)
import           Data.List.NonEmpty               (NonEmpty)
import qualified Data.List.NonEmpty               as N
import           Data.Monoid                      hiding (All, Any, Sum)
import           GHC.Exts

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Construct
import           Database.Algebra.Table.Lang

import qualified Database.DSH.Common.Lang         as L
import qualified Database.DSH.Common.Type         as T

import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Common.Impossible
import qualified Database.DSH.VL                  as VL

--------------------------------------------------------------------------------
-- Column names

-- | Item columns
ic :: Int -> Attr
ic i = "i" ++ show i

-- | Key columns
kc :: Int -> Attr
kc i = "k" ++ show i

-- | Order columns
oc :: Int -> Attr
oc i = "o" ++ show i

-- | Ref columns
rc :: Int -> Attr
rc i = "r" ++ show i

-- | (Key) source columns
sc :: Int -> Attr
sc i = "s" ++ show i

-- | (Key) destination columns
dc :: Int -> Attr
dc i = "d" ++ show i

-- | Grouping columns
gc :: Int -> Attr
gc i = "g" ++ show i

-- | Filter columns
fc :: Int -> Attr
fc i = "f" ++ show i

-- | Synthesized order column (left)
lsoc :: Attr
lsoc = "lso"

-- | Synthesized order column (right)
rsoc :: Attr
rsoc = "rso"

-- | Synthesized order column
soc :: Attr
soc = "so"

-- | Union side marker
usc :: Attr
usc = "us"

keyCols :: VecKey -> [Attr]
keyCols (VecKey i) = [ kc c | c <- [1..i] ]

ordCols :: VecOrder -> [Attr]
ordCols (VecOrder o) = [ oc c | c <- [1..] | _ <- o ]

refCols :: VecRef -> [Attr]
refCols (VecRef i) = [ rc c | c <- [1..i] ]

itemCols :: VecItems -> [Attr]
itemCols (VecItems i) = [ ic c | c <- [1..i] ]

filterCols :: VecFilter -> [Attr]
filterCols (VecFilter i) = [ fc c | c <- [1..i] ]

srcCols :: VecTransSrc -> [Attr]
srcCols (VecTransSrc i) = [ sc c | c <- [1..i] ]

--------------------------------------------------------------------------------
-- Projection

-- | Column projection: 'c'
cP :: Attr -> Proj
cP a = (a, ColE a)

-- | Expression projection 'c:e'
eP :: Attr -> Expr -> Proj
eP = (,)

-- | Mapping projection 'a:b'
mP :: Attr -> Attr -> Proj
mP n o = (n, ColE o)

keyProj :: VecKey -> [Proj]
keyProj (VecKey i) = map (cP . kc) [1..i]

ordProj :: VecOrder -> [Proj]
ordProj (VecOrder ds) = zipWith (\_ i -> cP (oc i)) ds [1..]

refProj :: VecRef -> [Proj]
refProj (VecRef 0) = []
refProj (VecRef i) = map (cP . rc) [1..i]

itemProj :: VecItems -> [Proj]
itemProj (VecItems 0) = []
itemProj (VecItems i) = map (cP . ic) [1..i]

-- srcProj :: VecTransSrc -> [Proj]
-- srcProj (VecTransSrc i) = map (cP . sc) [1..i]

filterProj :: VecKey -> [Proj]
filterProj (VecKey i) = [ mP (fc c) (kc c) | c <- [1..i] ]

-- | Generate a projection that shifts item names of a right input
-- vector to avoid collision with the items in the left input vector.
shiftItems :: VecItems -> VecItems -> [Proj]
shiftItems (VecItems li) (VecItems ri) =
    [ mP (ic (c + li)) (ic c) | c <- [1..ri] ]

-- | Generate a projection that shifts key columns of a right input
-- vector to avoid collision with the key columns in the left input
-- vector.
shiftKey :: VecKey -> VecKey -> [Proj]
shiftKey (VecKey lk) (VecKey rk) =
    [ mP (kc (c + lk)) (kc c) | c <- [1..rk] ]

-- | Generate a projection that shifts key columns of a right input
-- vector to avoid collision with the key columns in the left input
-- vector.
shiftRef :: VecRef -> VecRef -> [Proj]
shiftRef (VecRef lr) (VecRef rr) =
    [ mP (rc (c + lr)) (rc c) | c <- [1..rr] ]

-- | Generate a projection that shifts key columns of a right input
-- vector to avoid collision with the key columns in the left input
-- vector.
shiftOrd :: VecOrder -> VecOrder -> [Proj]
shiftOrd (VecOrder lo) (VecOrder ro) =
    [ mP (oc (c + length lo)) (oc c) | c <- [1..] | _ <- ro ]

shiftAll :: TADVec -> TADVec -> [Proj]
shiftAll (TADVec _ o1 k1 r1 i1) (TADVec _ o2 k2 r2 i2) =
    shiftOrd o1 o2 ++
    shiftKey k1 k2 ++
    shiftRef r1 r2 ++
    shiftItems i1 i2

-- | Generate a join predicate that joins two vectors by their keys.
keyJoin :: VecKey -> VecKey -> [(Expr, Expr, JoinRel)]
keyJoin (VecKey k1) (VecKey k2) = assert (k1 == k2)
    [ (ColE (kc c), ColE (kc (c + k1)), EqJ) | c <- [1..k1]]

-- | Generate a projection that maps key columns to source columns.
keySrcProj :: VecKey -> [Proj]
keySrcProj (VecKey i) = [ mP (sc c) (kc c) | c <- [1..i] ]

-- -- | Create the relational representation of a transformation vector
-- -- from a single data vector. The key is duplicated into source and
-- -- destination columns.
-- transProj :: VecKey -> [Proj]
-- transProj (VecKey i) = [ mP (sc c) (kc c) | c <- [1..i] ]
--                        ++
--                        [ mP (dc c) (kc c) | c <- [1..i] ]

-- | Generate the left propagation vector for a product-like operator.
prodTransProjLeft :: VecKey -> VecKey -> [Proj]
prodTransProjLeft k1 k2 =
    [ mP (sc c) (kc c) | c <- [1..unKey k1] ]
    ++
    [ mP (dc c) (kc c) | c <- [1..unKey (k1 <> k2)] ]

-- | Generate the right propagation vector for a product-like operator.
prodTransProjRight :: VecKey -> VecKey -> [Proj]
prodTransProjRight k1 k2 =
    [ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]
    ++
    [ mP (dc c) (kc c) | c <- [1..unKey (k1 <> k2)] ]

-- | Generate a projection that keeps all required columns of a vector
vecProj :: VecOrder -> VecKey -> VecRef -> VecItems -> [Proj]
vecProj o k r i = ordProj o ++ keyProj k ++ refProj r ++ itemProj i

chooseBaseKey :: N.NonEmpty L.Key -> NonEmpty Attr
chooseBaseKey keys = case sortWith (\(L.Key k) -> N.length k) $ N.toList keys of
    L.Key k : _ -> fmap (\(L.ColName c) -> c) k
    _           -> $impossible

keyRefProj :: VecKey -> [Proj]
keyRefProj (VecKey i) = [ mP (rc c) (kc c) | c <- [1..i] ]

--------------------------------------------------------------------------------
-- Expressions

algVal :: L.ScalarVal -> AVal
algVal (L.IntV i)     = int (fromIntegral i)
algVal (L.BoolV t)    = bool t
algVal L.UnitV        = int 0xdeadbeef
algVal (L.StringV s)  = string s
algVal (L.DoubleV d)  = double d
algVal (L.DateV d)    = date $ L.unDate d
algVal (L.DecimalV d) = dec d

binOp :: L.ScalarBinOp -> Expr -> Expr -> Expr
binOp (L.SBNumOp L.Add)       = BinAppE Plus
binOp (L.SBNumOp L.Sub)       = BinAppE Minus
binOp (L.SBNumOp L.Div)       = BinAppE Div
binOp (L.SBNumOp L.Mul)       = BinAppE Times
binOp (L.SBNumOp L.Mod)       = BinAppE Modulo
binOp (L.SBRelOp L.Eq)        = BinAppE Eq
binOp (L.SBRelOp L.NEq)       = BinAppE NEq
binOp (L.SBRelOp L.Gt)        = BinAppE Gt
binOp (L.SBRelOp L.GtE)       = BinAppE GtE
binOp (L.SBRelOp L.Lt)        = BinAppE Lt
binOp (L.SBRelOp L.LtE)       = BinAppE LtE
binOp (L.SBBoolOp L.Conj)     = BinAppE And
binOp (L.SBBoolOp L.Disj)     = BinAppE Or
binOp (L.SBStringOp L.Like)   = BinAppE Like
binOp (L.SBDateOp L.AddDays)  = flip $ BinAppE Plus
binOp (L.SBDateOp L.SubDays)  = flip $ BinAppE Minus
binOp (L.SBDateOp L.DiffDays) = flip $ BinAppE Minus

unOp :: L.ScalarUnOp -> UnFun
unOp (L.SUBoolOp L.Not)             = Not
unOp (L.SUCastOp L.CastDouble)      = Cast doubleT
unOp (L.SUCastOp L.CastDecimal)     = Cast decT
unOp (L.SUNumOp L.Sin)              = Sin
unOp (L.SUNumOp L.Cos)              = Cos
unOp (L.SUNumOp L.Tan)              = Tan
unOp (L.SUNumOp L.ASin)             = ASin
unOp (L.SUNumOp L.ACos)             = ACos
unOp (L.SUNumOp L.ATan)             = ATan
unOp (L.SUNumOp L.Sqrt)             = Sqrt
unOp (L.SUNumOp L.Exp)              = Exp
-- DSH uses the Haskell meaning of log, namely the natural logarithm.
unOp (L.SUNumOp L.Log)              = Ln
unOp (L.SUTextOp (L.SubString f t)) = SubString f t
unOp (L.SUDateOp L.DateDay)         = DateDay
unOp (L.SUDateOp L.DateMonth)       = DateMonth
unOp (L.SUDateOp L.DateYear)        = DateYear

taExprOffset :: Int -> VL.Expr -> Expr
taExprOffset o (VL.BinApp op e1 e2) = binOp op (taExprOffset o e1) (taExprOffset o e2)
taExprOffset o (VL.UnApp op e)      = UnAppE (unOp op) (taExprOffset o e)
taExprOffset o (VL.Column c)        = ColE $ ic $ c + o
taExprOffset _ (VL.Constant v)      = ConstE $ algVal v
taExprOffset o (VL.If c t e)        = IfE (taExprOffset o c) (taExprOffset o t) (taExprOffset o e)

taExpr :: VL.Expr -> Expr
taExpr = taExprOffset 0

--------------------------------------------------------------------------------

algTy :: T.ScalarType -> ATy
algTy T.IntT     = intT
algTy T.DoubleT  = doubleT
algTy T.BoolT    = boolT
algTy T.StringT  = stringT
algTy T.UnitT    = intT
algTy T.DateT    = dateT
algTy T.DecimalT = decT

aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum _ e) = Sum $ taExpr e
aggrFun (VL.AggrMin e)   = Min $ taExpr e
aggrFun (VL.AggrMax e)   = Max $ taExpr e
aggrFun (VL.AggrAvg e)   = Avg $ taExpr e
aggrFun (VL.AggrAll e)   = All $ taExpr e
aggrFun (VL.AggrAny e)   = Any $ taExpr e
aggrFun VL.AggrCount     = CountStar

-- | Map aggregate functions to relational aggregates for the
-- groupjoin operator. For Count, we need the first key column of the
-- right input to account for the NULLs produced by the outer join.:725
aggrFunGroupJoin :: Int -> VL.AggrFun -> AggrType
aggrFunGroupJoin _ (VL.AggrSum _ e) = Sum $ taExpr e
aggrFunGroupJoin _ (VL.AggrMin e)   = Min $ taExpr e
aggrFunGroupJoin _ (VL.AggrMax e)   = Max $ taExpr e
aggrFunGroupJoin _ (VL.AggrAvg e)   = Avg $ taExpr e
aggrFunGroupJoin _ (VL.AggrAll e)   = All $ taExpr e
aggrFunGroupJoin _ (VL.AggrAny e)   = Any $ taExpr e
aggrFunGroupJoin c VL.AggrCount     = Count $ ColE (kc c)

-- | Transform a VL join predicate into a TA predicate. Items of the
-- left input are necessary to account for the pre-join item column
-- shift in the right input.
joinPredicate :: VecItems -> L.JoinPredicate VL.Expr -> [(Expr, Expr, JoinRel)]
joinPredicate (VecItems o) (L.JoinPred conjs) =
    N.toList $ fmap (joinConjunct o) conjs

joinConjunct :: Int -> L.JoinConjunct VL.Expr -> (Expr, Expr, JoinRel)
joinConjunct o (L.JoinConjunct e1 op e2) = (taExpr e1, taExprOffset o e2, joinOp op)

refJoinPred :: VecRef -> [(Expr, Expr, JoinRel)]
refJoinPred (VecRef r) = [ (ColE $ rc c, ColE $ rc $ c + r, EqJ) | c <- [1..r] ]

joinOp :: L.BinRelOp -> JoinRel
joinOp L.Eq  = EqJ
joinOp L.Gt  = GtJ
joinOp L.GtE = GeJ
joinOp L.Lt  = LtJ
joinOp L.LtE = LeJ
joinOp L.NEq = NeJ

windowFunction :: VL.WinFun -> WinFun
windowFunction (VL.WinSum e)        = WinSum $ taExpr e
windowFunction (VL.WinMin e)        = WinMin $ taExpr e
windowFunction (VL.WinMax e)        = WinMax $ taExpr e
windowFunction (VL.WinAvg e)        = WinAvg $ taExpr e
windowFunction (VL.WinAll e)        = WinAll $ taExpr e
windowFunction (VL.WinAny e)        = WinAny $ taExpr e
windowFunction (VL.WinFirstValue e) = WinFirstValue $ taExpr e
windowFunction VL.WinCount          = WinCount

frameSpecification :: VL.FrameSpec -> FrameBounds
frameSpecification VL.FAllPreceding   = ClosedFrame FSUnboundPrec FECurrRow
frameSpecification (VL.FNPreceding n) = ClosedFrame (FSValPrec n) FECurrRow

--------------------------------------------------------------------------------

-- | The default value for sums over empty lists for all possible
-- numeric input types.
sumDefault :: T.ScalarType -> (ATy, AVal)
sumDefault T.IntT     = (AInt, int 0)
sumDefault T.DoubleT  = (ADouble, double 0)
sumDefault T.DecimalT = (ADec, dec 0)
sumDefault _          = $impossible

groupJoinDefault :: AlgNode
                 -> VecOrder
                 -> VecKey
                 -> VecRef
                 -> VecItems
                 -> AVal
                 -> Build TableAlgebra AlgNode
groupJoinDefault qa o k r i defaultVal =
    proj (vecProj o k r i
          ++
          [eP acol (BinAppE Coalesce (ColE acol) (ConstE defaultVal))])
         qa
  where
    acol  = ic (unItems i + 1)

-- | For a segmented aggregate operator, apply the aggregate
-- function's default value for the empty segments. The first argument
-- specifies the outer vector, while the second argument specifies the
-- result vector of the aggregate.
--
-- Note: AggrS produces regular vector with singleton segments. For
-- key and order of this vector, we can not use the inner key and
-- order of the aggregation result, as the values for the empty
-- segments are missing. Also, we can not mix in order and key values
-- of the outer vector, because they might not be aligned at
-- all. Instead, we generate surrogate values for order and key based
-- on the ref values. This is necessary to keep the vector
-- presentation uniform, but we can statically say that these
-- rownum-generated values will not be used: the aggregation default
-- has to be unboxed and unboxing will discard inner key and order.
--
-- FIXME employ an outerjoin-based scheme for default values based on
-- the unbox operator.
segAggrDefault :: AlgNode -> AlgNode -> VecKey -> VecRef -> AVal -> Build TableAlgebra AlgNode
segAggrDefault qo qa ok r defaultValue =
    -- Generate synthetic ord and key values for the inner vector.
    projM ([cP (oc 1), mP (kc 1) (oc 1)] ++ refProj r ++ [cP (ic 1)])
    $ rownumM (oc 1) (refCols r) []
    $ proj (refProj r ++ itemProj (VecItems 1)) qa
      `unionM`
      projM (refProj r ++ [eP (ic 1) (ConstE defaultValue)])
           -- We know that the outer key must be aligned with inner references.
           (differenceM
               (proj (keyRefProj ok) qo)
               (proj (refProj r) qa))

aggrDefault :: AlgNode -> AVal -> Build TableAlgebra AlgNode
aggrDefault qa defaultVal =
    proj [cP (oc 1), cP (kc 1), cP (rc 1), eP (ic 1) defaultExpr] qa

  where
    defaultExpr = BinAppE Coalesce (ColE (ic 1)) (ConstE defaultVal)

flipDir :: SortDir -> SortDir
flipDir Asc  = Desc
flipDir Desc = Asc

synthOrder :: VecOrder -> [SortSpec]
synthOrder (VecOrder dirs) = [ (ColE $ oc c, d)| c <- [1..] | d <- dirs ]

--------------------------------------------------------------------------------

-- | The VectorAlgebra instance for TA algebra, implemented using
-- natural keys.
instance VL.VectorAlgebra TableAlgebra where
    type DVec TableAlgebra = TADVec
    type RVec TableAlgebra = TARVec
    type KVec TableAlgebra = TAKVec
    type FVec TableAlgebra = TAFVec
    type SVec TableAlgebra = TASVec

    vecWinFun a w (TADVec q o k r i) = do
        let wfun      = windowFunction a
            frameSpec = frameSpecification w
            winCol    = ic $ unItems i + 1
        qw <- winFun (winCol, wfun) [] (synthOrder o) (Just frameSpec) q
        return $ TADVec qw o k r (i <> VecItems 1)

    vecUniqueS (TADVec q o k r i) = do
        -- Create per-segment groups based on the items and select the
        -- first member of each group
        qu <- projM (ordProj o ++ keyProj k ++ refProj r ++ itemProj i)
              $ selectM (BinAppE Eq (ColE soc) (ConstE $ VInt 1))
              $ rownum soc (ordCols o) (map ColE $ refCols r ++ itemCols i) q

        return $ TADVec qu o k r i

    -- FIXME we might have key order for inner vectors. include the
    -- key here.
    vecNumberS (TADVec q o@(VecOrder ds) k r i) = do
        let i' = VecItems (unItems i + 1)
            nc = ic (unItems i + 1)

        qn <- rownum' nc
                      [ (ColE c, d) | c <- ordCols o | d <- ds ]
                      (map ColE (refCols r)) q
        return $ TADVec qn o k r i'

    -- FIXME does flipping the direction really implement reversing of
    -- the order?
    vecReverseS (TADVec q (VecOrder ds) k r i) = do
        let o' = VecOrder $ map flipDir ds
        return ( TADVec q o' k r i
               , TASVec
               )

    -- Per-segment sorting is no different from regular sorting
    -- because we require only relative per-segment order in inner
    -- vectors.
    vecSortS sortExprs (TADVec q o k r i) = do
        let o'       = VecOrder (map (const Asc) sortExprs) <> o
            -- Include the old order columns. This implements stable
            -- sorting and guarantees a strict total order of columns.
            sortCols = [ eP (oc c) (taExpr e) | c <- [1..] | e <- sortExprs ]
                       ++
                       [ mP (oc (c + length sortExprs)) (oc c)
                       | c <- [1..unOrd o]
                       ]

        qe <- proj (sortCols ++ keyProj k ++ refProj r ++ itemProj i) q
        return ( TADVec qe o' k r i
               , TASVec
               )

    vecThetaJoinS p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = r1         -- The left vector defines the reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (vecProj o k r i)
               $ thetaJoinM (refJoinPred r1 ++ joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecCartProductS v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = r1         -- The left vector defines the reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (vecProj o k r i)
               $ thetaJoinM (refJoinPred r1)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecSemiJoinS p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1

        qj <- semiJoinM (refJoinPred r1 ++ joinPredicate i1 p)
                    (return q1)
                    (proj (shiftAll v1 v2) q2)

        qf <- proj (filterProj k1) qj

        return ( TADVec qj o k r i
               , TAFVec qf (VecFilter $ unKey k1)
               )

    vecAntiJoinS p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1

        qj <- antiJoinM (refJoinPred r1 ++ joinPredicate i1 p)
                    (return q1)
                    (proj (shiftAll v1 v2) q2)

        qf <- proj (filterProj k1) qj

        return ( TADVec qj o k r i
               , TAFVec qf (VecFilter $ unKey k1)
               )

    vecNestJoinS p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = keyRef k1  -- Nesting operator: left vector defines reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- thetaJoinM (refJoinPred r1 ++ joinPredicate i1 p)
                   (return q1)
                   (proj (shiftAll v1 v2) q2)

        qd  <- proj (ordProj o ++ keyProj k ++ keyRefProj k1 ++ itemProj i) qj
        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qd o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecNestProductS v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = keyRef k1  -- Nesting operator: left vector defines reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- thetaJoinM (refJoinPred r1)
                   (return q1)
                   (proj (shiftAll v1 v2) q2)

        qd  <- proj (ordProj o ++ keyProj k ++ keyRefProj k1 ++ itemProj i) qj
        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qd o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecGroupJoin p a v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1 <> VecItems 1

        let acol      = ic (unItems i1 + 1)
            groupCols = [ (c, ColE c)
                        | c <- keyCols k1 ++ ordCols o1 ++ refCols r1 ++ itemCols i1
                        ]

        let join = case a of
                         VL.AggrSum _ _ -> leftOuterJoinM
                         VL.AggrAny _   -> leftOuterJoinM
                         VL.AggrAll _   -> leftOuterJoinM
                         VL.AggrCount   -> leftOuterJoinM
                         VL.AggrMax _   -> thetaJoinM
                         VL.AggrMin _   -> thetaJoinM
                         VL.AggrAvg _   -> thetaJoinM

        qa  <- projM (ordProj o ++ keyProj k ++ refProj r1 ++ itemProj i)
               $ aggrM [(aggrFunGroupJoin (unKey k1 + 1) a, acol)] groupCols
               $ join (joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qd <- case a of
                  VL.AggrSum t _ -> groupJoinDefault qa o k r i1 (snd $ sumDefault t)
                  VL.AggrAny _   -> groupJoinDefault qa o k r i1 (bool False)
                  VL.AggrAll _   -> groupJoinDefault qa o k r i1 (bool True)
                  _              -> return qa

        return $ TADVec qd o k r i

    vecAggr a (TADVec q _ _ _ _) = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = VecRef 1
            i = VecItems 1

        let oneE = ConstE $ int 1

        qa <- projM [eP (oc 1) oneE, eP (kc 1) oneE, eP (rc 1) oneE, cP (ic 1)]
              $ aggr [(aggrFun a, ic 1)] [] q

        qd <- case a of
                  VL.AggrSum t _ -> aggrDefault qa (snd $ sumDefault t)
                  VL.AggrAll _   -> aggrDefault qa (bool True)
                  VL.AggrAny _   -> aggrDefault qa (bool False)
                  -- SQL COUNT handles empty inputs.
                  VL.AggrCount   -> return qa
                  -- All other aggregates can not be handled correctly.
                  _              -> return qa

        return $ TADVec qd o k r i

    vecAggrS a (TADVec qo _ k1 _ _) (TADVec qi _ _ r2 _) = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = r2
            i = VecItems 1
        -- Group the inner vector by ref.
        qa <- aggr [(aggrFun a, ic 1)] [ (c, ColE c) | c <- refCols r2 ] qi
        qd <- case a of
                  VL.AggrSum t _ -> segAggrDefault qo qa k1 r2 (snd $ sumDefault t)
                  VL.AggrAny _   -> segAggrDefault qo qa k1 r2 (bool False)
                  VL.AggrAll _   -> segAggrDefault qo qa k1 r2 (bool True)
                  VL.AggrCount   -> segAggrDefault qo qa k1 r2 (int 0)
                  _              ->
                      projM ([cP (oc 1), mP (kc 1) (oc 1)]
                             ++ refProj r
                             ++ itemProj i)
                      $ rownum (oc 1) (refCols r) [] qa

        return $ TADVec qd o k r i

    vecGroupAggr groupExprs aggrFuns (TADVec q _ _ _ _) = do
        let gl = length groupExprs
        let o' = VecOrder $ replicate gl Asc
            k' = VecKey gl
            r' = VecRef 0
            i' = VecItems $ length groupExprs + N.length aggrFuns

        let parts = [ eP (ic c) (taExpr e) | e <- groupExprs | c <- [1..]]

            aggrs = [ (aggrFun a, ic i) | a <- N.toList aggrFuns | i <- [gl+1..] ]

        let ordProjs = [ mP (oc c) (ic c) | c <- [1..unItems i'] ]
            keyProjs = [ mP (kc c) (ic c) | c <- [1..unItems i'] ]

        qa <- projM (ordProjs ++ keyProjs ++ itemProj i')
              $ aggr aggrs parts q

        return $ TADVec qa o' k' r' i'

    vecGroupS groupExprs (TADVec q o k r i) = do
        let gl = length groupExprs
        let o1 = VecOrder $ replicate gl Asc
            k1 = VecKey $ unRef r + gl
            r1 = r
            i1 = VecItems gl

        let o2 = o
            k2 = k
            r2 = VecRef $ unRef r + gl
            i2 = i

        -- Apply the grouping expressions
        let groupCols  = [ gc c | c <- [1..] | _ <- groupExprs ]
            groupProj  = [ eP g (taExpr ge) | g <- groupCols | ge <- groupExprs ]

        qg <- proj (vecProj o k r i ++ groupProj) q

        -- Generate the outer vector: one tuple per distinct values of
        -- the ref and grouping columns.
        let outerKeyProj = [ mP (kc c) g | c <- [1..] | g <- refCols r ++ groupCols ]
            outerOrdProj = [ mP (oc c) g | c <- [1..] | g <- groupCols ]
            outerItemProj = [ mP (ic c) g | c <- [1..] | g <- groupCols ]

        qo <- projM (outerOrdProj ++ outerKeyProj ++ refProj r ++ outerItemProj)
              $ distinctM
              $ proj (refProj r ++ [ cP g | g <- groupCols ]) qg

        -- Generate the inner vector that references the groups in the
        -- outer vector.
        let innerRefProj = [ mP (rc c) g | c <- [1..] | g <- refCols r ++ groupCols ]
        qi <- proj (ordProj o ++ keyProj k ++ innerRefProj ++ itemProj i) qg

        return ( TADVec qo o1 k1 r1 i1
               , TADVec qi o2 k2 r2 i2
               , TASVec
               )

    vecAlign (TADVec q1 o1 k1 r1 i1) (TADVec q2 _ k2 _ i2) = do
        -- Join both vectors by their keys. Because this is a
        -- 1:1-join, we can discard order and ref of the right input.
        qa <- projM (ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj (i1 <> i2))
              $ thetaJoinM (keyJoin k1 k2)
                    (return q1)
                    (proj (shiftKey k1 k2 ++ shiftItems i1 i2) q2)
        return $ TADVec qa o1 k1 r1 (i1 <> i2)

    vecSelect expr (TADVec q o k r i) = do
        qs <- select (taExpr expr) q
        qr <- proj (filterProj k) qs
        return ( TADVec qs o k r i
               , TAFVec qr (VecFilter $ unKey k)
               )

    vecZip (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 _ i2) = do
        let -- The result vector uses synthetic rownum-generated order
            -- and keys
            o = VecOrder [Asc]
            k = VecKey 1
            r = r1
            i = i1 <> i2

        qj <- thetaJoinM [(ColE lsoc, ColE rsoc, EqJ)]
                  (rownum' lsoc (synthOrder o1) [] q1)
                  (projM ([cP rsoc] ++ shiftKey k1 k2 ++ shiftItems i1 i2)
                   $ rownum' rsoc (synthOrder o2) [] q2)

        let keyProj1 = mP (dc 1) lsoc : [ mP (sc c) (kc c) | c <- [1..unKey k1]]
            keyProj2 = mP (dc 1) lsoc
                       :
                       [ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]
        qk1 <- proj keyProj1 qj
        qk2 <- proj keyProj2 qj
        qd  <- proj ([mP (oc 1) lsoc, mP (kc 1) lsoc] ++ refProj r1 ++ itemProj i) qj

        return ( TADVec qd o k r i
               , TAKVec qk1 (VecTransSrc $ unKey k1) (VecTransDst 1)
               , TAKVec qk2 (VecTransSrc $ unKey k2) (VecTransDst 1)
               )

    vecZipS (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 r2 i2) = do
        let -- The result vector uses synthetic rownum-generated
            -- per-segment order. As key, we can simply use the key
            -- from either left or right side. Both will retain their
            -- key property as we are doing a 1:1 join.
            o = VecOrder [Asc]
            k = k1
            r = r1
            i = i1 <> i2

        qj <- thetaJoinM ( (ColE lsoc, ColE rsoc, EqJ) : refJoinPred r1)
                  (rownum' lsoc (synthOrder o1) (map ColE $ refCols r1) q1)
                  (projM ([cP rsoc] ++ shiftKey k1 k2 ++ shiftRef r1 r2 ++ shiftItems i1 i2)
                   $ rownum' rsoc (synthOrder o2) (map ColE $ refCols r2) q2)

        let keyProj1 = [ mP (dc c) (kc c) | c <- [1..unKey k1] ]
                       ++
                       [ mP (sc c) (kc c) | c <- [1..unKey k1] ]
            keyProj2 = [ mP (dc c) (kc c) | c <- [1..unKey k1] ]
                       ++
                       [ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]

        qk1 <- proj keyProj1 qj
        qk2 <- proj keyProj2 qj
        qd  <- proj ([mP (oc 1) lsoc] ++ keyProj k ++ refProj r1 ++ itemProj i) qj

        return ( TADVec qd o k r i
               , TAKVec qk1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k1)
               , TAKVec qk2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k1)
               )

    vecProject exprs (TADVec q o k r _) = do
        let items = zipWith (\c e -> eP (ic c) (taExpr e)) [1..] exprs
        qp <- proj (ordProj o ++ keyProj k ++ refProj r ++ items) q
        return $ TADVec qp o k r (VecItems $ length items)

    vecTableRef tableName schema = do
        q <- projM (baseKeyProj ++ baseOrdProj ++ baseItemProj)
             $ dbTable tableName taColumns taKeys
        return $ TADVec q order key ref items

      where
        -- Columns and keys for the TA table operator
        taColumns = [ (c, algTy t)
                    | (L.ColName c, t) <- N.toList $ L.tableCols schema
                    ]

        taKeys =    [ Key [ c | L.ColName c <- N.toList k ]
                    | L.Key k <- N.toList $ L.tableKeys schema
                    ]

        -- We choose one key heuristically and use it to induce order.
        baseKeyCols  = chooseBaseKey (L.tableKeys schema)
        (baseKeyProj, baseOrdProj)
                     = unzip [ (mP (kc i) c, mP (oc i) c)
                             | i <- [1..]
                             | c <- N.toList baseKeyCols
                             ]
        baseItemProj = [ mP (ic i) c | i <- [1..] | (c, _) <- taColumns ]

        items = VecItems $ N.length $ L.tableCols schema
        order = VecOrder $ const Asc <$> N.toList baseKeyCols
        key   = VecKey $ N.length baseKeyCols
        ref   = VecRef 0

    vecLit tys frame segments = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = VecRef 1
            i = VecItems (length tys)

        let refCol = mkRefCol segments
            keyCol = map (L.IntV . snd) $ zip refCol [1..]
            -- The schema for a vector literal consists of key and ref columns
            -- and all payload columns.
            litSchema = [(rc 1, intT), (kc 1, intT)]
                        ++
                        [ (ic c, algTy t) | c <- [1..] | t <- tys ]
            cols   = refCol : keyCol : VL.vectorCols tys segments
            rows   = transpose cols

        qr <- projM ([mP (oc 1) (kc 1), cP (kc 1), cP (rc 1)] ++ itemProj i)
              $ litTable' (map (map algVal) rows) litSchema
        return $ TADVec qr o k r i

      where
        -- Create a ref column with the proper length from the segment
        -- description.
        mkRefCol (VL.UnitSeg _) = replicate (VL.frameLen frame) (L.IntV 1)
        -- For a vector with multiple segments, we enumerate the segments to get
        -- segment identifiers and replicate those according to the length of
        -- the segment. Note that segments also contain empty segments, i.e.
        -- every segment identifier is obtained from the list of segments and
        -- matches the key in the outer vector.
        mkRefCol (VL.Segs segs) = concat [ replicate (VL.segLen s) (L.IntV si)
                                         | (s, si) <- zip segs [1..]
                                         ]

    vecAppend (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 r2 i2) = do
        -- We have to use synthetic rownum-generated order and keys
        -- because left and right inputs might have non-compatible
        -- order and keys.

        -- Create synthetic order keys based on the original order
        -- columns and a marker column for left and right inputs.
        qs1 <- projM ([eP usc (ConstE $ VInt 1), cP soc]
                      ++ ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj i1)
               $ rownum' soc (synthOrder o1) [] q1

        -- Generate a rekeying vector that maps old keys to new synthetic ones.
        qk1 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k1) qs1

        -- Generate the union input for the left side: We use the
        -- marker column together with the rownum-generated values as
        -- order and keys.
        qu1 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 1) usc, mP (kc 2) soc]
                     ++ refProj r1 ++ itemProj i1)
                    qs1

        -- Do the same for the right input.
        qs2 <- projM ([eP usc (ConstE $ VInt 2), cP soc]
                      ++ ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i2)
               $ rownum' soc (synthOrder o2) [] q2
        qk2 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k2) qs2

        qu2 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 1) usc, mP (kc 2) soc]
                     ++ refProj r2 ++ itemProj i2)
                    qs2

        -- With synthetic order and key values, both inputs are
        -- schema-compatible and can be used in a union.
        qu <- qu1 `union` qu2

        return ( TADVec qu (VecOrder [Asc, Asc]) (VecKey 2) r1 i1
               , TAKVec qk1 (VecTransSrc $ unKey k1) (VecTransDst 2)
               , TAKVec qk2 (VecTransSrc $ unKey k2) (VecTransDst 2)
               )

    vecAppendS (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 r2 i2) = do
        -- We have to use synthetic rownum-generated order and keys
        -- because left and right inputs might have non-compapible
        -- order and keys.

        -- Create synthetic order keys based on the original order
        -- columns and a marker column for left and right
        -- inputs. Order for inner vectors might not be key
        -- (per-segment order), so we have to include the key here to
        -- avoid random results.
        qs1 <- projM ([eP usc (ConstE $ VInt 1), cP soc]
                      ++ ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj i1)
               $ rownum' soc
                         (synthOrder o1 ++ map (\c -> (ColE c, Asc)) (keyCols k1))
                         []
                         q1

        -- Generate a rekeying vector that maps old keys to
        qk1 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k1) qs1

        -- Generate the union input for the left side: We use the
        -- marker column together with the rownum-generated values as
        -- order and keys.
        qu1 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 1) usc, mP (kc 2) soc]
                     ++ refProj r1 ++ itemProj i1)
                    qs1

        -- Do the same for the right input.
        qs2 <- projM ([eP usc (ConstE $ VInt 2), cP soc]
                      ++ ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i2)
               $ rownum' soc
                         (synthOrder o2 ++ map (\c -> (ColE c, Asc)) (keyCols k2))
                         []
                         q2
        qk2 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k2) qs2

        qu2 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 2) usc, mP (kc 2) soc]
                     ++ refProj r2 ++ itemProj i2)
                    qs2

        -- With synthetic order and key values, both inputs are
        -- schema-compatible and can be used in a union.
        qu <- qu1 `union` qu2

        return ( TADVec qu (VecOrder [Asc, Asc]) (VecKey 2) r1 i1
               , TAKVec qk1 (VecTransSrc $ unKey k1) (VecTransDst 2)
               , TAKVec qk2 (VecTransSrc $ unKey k2) (VecTransDst 2)
               )

    -- FIXME can we really rely on keys being aligned/compatible?
    vecCombine (TADVec qb ob kb rb _)
               (TADVec q1 _ k1 _ i1)
               (TADVec q2 _ k2 _ i2) = do

        d1  <- thetaJoinM [ (ColE $ kc c, ColE $ kc $ c + unKey kb, EqJ)
                          | c <- [1..unKey k1]
                          ]
                   (projM (ordProj ob ++ keyProj kb ++ refProj rb)
                    $ select (ColE (ic 1)) qb)
                   (proj (shiftKey kb k1 ++ itemProj i1) q1)

        d2  <- thetaJoinM [ (ColE $ kc c, ColE $ kc $ c + unKey kb, EqJ)
                          | c <- [1..unKey k2]
                          ]
                   (projM (ordProj ob ++ keyProj kb ++ refProj rb)
                    $ select (UnAppE Not (ColE (ic 1))) qb)
                   (proj (shiftKey kb k2 ++ itemProj i2) q2)

        qu  <- unionM
                   (proj (ordProj ob ++ keyProj kb ++ refProj rb ++ itemProj i1) d1)
                   (proj (ordProj ob ++ keyProj kb ++ refProj rb ++ itemProj i2) d2)

        qk1 <- proj ([ mP (sc c) (kc $ c + unKey kb) | c <- [1..unKey k1] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey kb] ])
                    d1

        qk2 <- proj ([ mP (sc c) (kc $ c + unKey kb) | c <- [1..unKey k2] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey kb] ])
                    d2

        return ( TADVec qu ob kb rb i1
               , TAKVec qk1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey kb)
               , TAKVec qk2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey kb)
               )

    -- Because we only demand per-segment order for inner vectors,
    -- reordering is a NOOP in the natural key model.
    vecAppSort _ dv = return (dv, TASVec)

    vecAppFilter (TAFVec qf f) (TADVec q o k r i) = do
        let filterPred = [ (ColE c1, ColE c2, EqJ)
                         | c1 <- refCols r
                         | c2 <- filterCols f
                         ]
        qj  <- semiJoin filterPred q qf
        qf' <- proj [ mP (fc c) (kc c) | c <- [1..unKey k] ] qj

        return ( TADVec qj o k r i
               , TAFVec qf' (VecFilter $ unKey k)
               )

    vecAppRep (TARVec qr s d) (TADVec q o k r i) = do
        let o' = o
            k' = k <> (VecKey $ unDst d)
            r' = VecRef $ unDst d
            i' = i

        let s' = VecTransSrc $ unKey k
            d' = VecTransDst $ unKey k'

        let repPred = [ (ColE c1, ColE c2, EqJ)
                      | c1 <- refCols r
                      | c2 <- srcCols s
                      ]
        qj  <- thetaJoin repPred q qr

        let newKeyProj = keyProj k
                         ++
                         [ mP (kc $ c + unKey k) (dc c)
                         | c <- [1..unDst d]
                         ]
            newRefProj = [ mP (rc c) (dc c) | c <- [1..unDst d] ]
        qd  <- proj (ordProj o' ++ newKeyProj ++ newRefProj ++ itemProj i)  qj
        qr' <- proj ([ mP (sc c) (kc c) | c <- [1..unKey k] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey k'] ])
                    qd


        return ( TADVec qd o' k' r' i'
               , TARVec qr' s' d'
               )

    vecAppKey (TAKVec qk s d) (TADVec q o k r i) = do
        let o' = o
            k' = k
            r' = VecRef $ unDst d
            i' = i

        let s' = VecTransSrc $ unKey k
            d' = VecTransDst $ unKey k

        let repPred = [ (ColE c1, ColE c2, EqJ)
                      | c1 <- refCols r
                      | c2 <- srcCols s
                      ]
        qj  <- thetaJoin repPred q qk

        let newRefProj = [ mP (rc c) (dc c) | c <- [1..unDst d] ]
        qd  <- proj (ordProj o' ++ keyProj k ++ newRefProj ++ itemProj i)  qj
        qr' <- proj ([ mP (sc c) (kc c) | c <- [1..unKey k] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey k] ])
                    qd

        return ( TADVec qd o' k' r' i'
               , TAKVec qr' s' d'
               )

    vecUnboxKey (TADVec q _ k r _) = do
        let mapSrcProj = [ mP (sc c) (kc c) | c <- [1..unKey k] ]
            mapDstProj = [ mP (dc c) (rc c) | c <- [1..unRef r] ]

        qk <- proj (mapSrcProj ++ mapDstProj) q
        return $ TAKVec qk (VecTransSrc $ unKey k) (VecTransDst $ unRef r)

    vecSegment (TADVec q o k _ i) = do
        let mapRefProj = [ mP (rc c) (kc c) | c <- [1..unKey k]]
        qi <- proj (ordProj o ++ keyProj k ++ mapRefProj ++ itemProj i) q
        return $ TADVec qi o k (VecRef $ unKey k) i

    vecUnsegment (TADVec q o k _ i) = do
        let constRefProj = [ eP (rc 1) (ConstE $ int 1) ]
        qi <- proj (ordProj o ++ keyProj k ++ constRefProj ++ itemProj i) q
        return $ TADVec qi o k (VecRef 1) i

    vecNest (TADVec q o k _ i) = do
        qo <- litTable' [[int 1, int 1]] [(oc 1, intT), (kc 1, intT)]
        let constRef = [eP (rc 1) (ConstE (int 1))]
        qi <- proj (ordProj o ++ keyProj k ++ constRef ++ itemProj i) q
        return ( TADVec qo (VecOrder [Asc]) (VecKey 1) (VecRef 0) (VecItems 0)
               , TADVec qi o k (VecRef 1) i
               )

    vecUnboxSng v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ k2 _ i2) = do
        let o = o1
            k = k1
            r = r1
            i = i1 <> i2

        qj <- thetaJoinM [ (ColE $ kc c, ColE $ rc $ c + unRef r1, EqJ)
                         | c <- [1..unKey k]
                         ]
                   (return q1)
                   (proj (shiftAll v1 v2) q2)

        qv <- proj (vecProj o k r i) qj
        qk <- proj ([ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k1] ])
                   qj

        return ( TADVec qv o k r i
               , TAKVec qk (VecTransSrc $ unKey k2) (VecTransDst $ unKey k1)
               )

    vecReplicateScalar (TADVec q1 _ k1 _ i1) (TADVec q2 o2 k2 r2 i2) = do
        let o = o2
            k = k2
            r = r2
            i = i1 <> i2

            s = VecTransSrc $ unKey k1
            d = VecTransDst $ unKey k2

        qp <- crossM
                  (proj (shiftKey k2 k1 ++ itemProj i1) q1)
                  (proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ shiftItems i1 i2) q2)

        qd <- proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i) qp
        qr <- proj ([ mP (sc c) (kc $ c + unKey k2) | c <- [1..unKey k1] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k2] ])
                   qp

        return ( TADVec qd o k r i
               , TARVec qr s d
               )

    vecReplicateNest (TADVec q1 _ k1 _ i1) (TADVec q2 o2 k2 r2 i2) = do
        let o = o2
            k = k2
            r = r2
            i = i1 <> i2

            s = VecTransSrc $ unKey k1
            d = VecTransDst $ unKey k2

        qj <- thetaJoinM [ (ColE (kc $ c + unKey k2), ColE (rc c), EqJ)
                         | c <- [1..unRef r2]
                         ]
                   (proj (shiftKey k2 k1 ++ itemProj i1) q1)
                   (proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ shiftItems i1 i2) q2)

        qd <- proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i) qj
        qr <- proj ([ mP (sc c) (kc $ c + unKey k2) | c <- [1..unKey k1] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k2] ])
                   qj

        return ( TADVec qd o k r i
               , TARVec qr s d
               )
