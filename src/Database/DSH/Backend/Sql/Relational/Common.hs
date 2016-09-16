{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- | Implementation of vector primitives in terms of relational algebra
-- using composite natural keys.
module Database.DSH.Backend.Sql.Relational.Common where

import           Control.Exception.Base
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
import qualified Database.DSH.SL                  as SL

{-# ANN module "HLint: ignore Reduce duplication" #-}

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

srcProj :: VecTransSrc -> [Proj]
srcProj (VecTransSrc i) = map (cP . sc) [1..i]

dstProj :: VecTransDst -> [Proj]
dstProj (VecTransDst i) = map (cP . sc) [1..i]

-- srcProj :: VecTransSrc -> [Proj]
-- srcProj (VecTransSrc i) = map (cP . sc) [1..i]

filterProj :: VecKey -> [Proj]
filterProj (VecKey i) = [ mP (fc c) (kc c) | c <- [1..i] ]

identityMapProj :: VecKey -> [Proj]
identityMapProj (VecKey k) = [ mP (sc c) (kc c) | c <- [1..k] ]
                             ++
                             [ mP (dc c) (kc c) | c <- [1..k] ]

-- | Generate a projection that shifts source column names of a right input
-- segment map to avoid collision with the items in the left input segment map.
shiftSrc :: VecTransSrc -> VecTransSrc -> [Proj]
shiftSrc (VecTransSrc ls) (VecTransSrc rs) =
    [ mP (sc (c + ls)) (sc c) | c <- [1..rs] ]

-- | Generate a projection that shifts destination column names of a right input
-- segment map to avoid collision with the items in the left input segment map.
shiftDst :: VecTransDst -> VecTransDst -> [Proj]
shiftDst (VecTransDst ld) (VecTransDst rd) =
    [ mP (dc (c + ld)) (dc c) | c <- [1..rd] ]

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

taExprOffset :: Int -> SL.Expr -> Expr
taExprOffset o (SL.BinApp op e1 e2) = binOp op (taExprOffset o e1) (taExprOffset o e2)
taExprOffset o (SL.UnApp op e)      = UnAppE (unOp op) (taExprOffset o e)
taExprOffset o (SL.Column c)        = ColE $ ic $ c + o
taExprOffset _ (SL.Constant v)      = ConstE $ algVal v
taExprOffset o (SL.If c t e)        = TernaryAppE If (taExprOffset o c)
                                                     (taExprOffset o t)
                                                     (taExprOffset o e)

pattern (:<=:) :: Expr -> Expr -> Expr
pattern e1 :<=: e2 <- BinAppE LtE e1 e2

pattern (:>=:) :: Expr -> Expr -> Expr
pattern e1 :>=: e2 <- BinAppE GtE e1 e2

pattern (:&&:) :: Expr -> Expr -> Expr
pattern e1 :&&: e2 = BinAppE And e1 e2

specializeExpr :: Expr -> Expr
specializeExpr e = case e of
    (e1 :>=: e2) :&&: (e1' :<=: e3) | e1 == e1' -> TernaryAppE Between e1 e2 e3
    (e1 :<=: e2) :&&: (e1' :>=: e3) | e1 == e1' -> TernaryAppE Between e1 e3 e2
    (e1 :<=: e2) :&&: ((e1' :>=: e3) :&&: e4) | e1 == e1' -> TernaryAppE Between e1 e3 e2 :&&: e4
    (e1 :>=: e2) :&&: ((e1' :<=: e3) :&&: e4) | e1 == e1' -> TernaryAppE Between e1 e2 e3 :&&: e4
    BinAppE f e1 e2 -> BinAppE f (specializeExpr e1) (specializeExpr e2)
    UnAppE f e1 -> UnAppE f (specializeExpr e1)
    ColE a -> ColE a
    ConstE v -> ConstE v
    TernaryAppE f e1 e2 e3 -> TernaryAppE f (specializeExpr e1) (specializeExpr e2) (specializeExpr e3)

taExpr :: SL.Expr -> Expr
taExpr = specializeExpr . taExprOffset 0

--------------------------------------------------------------------------------

algTy :: T.ScalarType -> ATy
algTy T.IntT     = intT
algTy T.DoubleT  = doubleT
algTy T.BoolT    = boolT
algTy T.StringT  = stringT
algTy T.UnitT    = intT
algTy T.DateT    = dateT
algTy T.DecimalT = decT

aggrFun :: SL.AggrFun -> AggrType
aggrFun (SL.AggrSum _ e)         = Sum $ taExpr e
aggrFun (SL.AggrMin e)           = Min $ taExpr e
aggrFun (SL.AggrMax e)           = Max $ taExpr e
aggrFun (SL.AggrAvg e)           = Avg $ taExpr e
aggrFun (SL.AggrAll e)           = All $ taExpr e
aggrFun (SL.AggrAny e)           = Any $ taExpr e
aggrFun (SL.AggrCountDistinct e) = CountDistinct $ taExpr e
aggrFun SL.AggrCount             = CountStar

-- | Map aggregate functions to relational aggregates for the
-- groupjoin operator. For Count, we need the first key column of the
-- right input to account for the NULLs produced by the outer join.
aggrFunGroupJoin :: Int -> SL.AggrFun -> AggrType
aggrFunGroupJoin _ (SL.AggrSum _ e)         = Sum $ taExpr e
aggrFunGroupJoin _ (SL.AggrMin e)           = Min $ taExpr e
aggrFunGroupJoin _ (SL.AggrMax e)           = Max $ taExpr e
aggrFunGroupJoin _ (SL.AggrAvg e)           = Avg $ taExpr e
aggrFunGroupJoin _ (SL.AggrAll e)           = All $ taExpr e
aggrFunGroupJoin _ (SL.AggrAny e)           = Any $ taExpr e
aggrFunGroupJoin c SL.AggrCount             = Count $ ColE (kc c)
aggrFunGroupJoin _ (SL.AggrCountDistinct e) = CountDistinct $ taExpr e

-- | Transform a SL.join predicate into a TA predicate. Items of the
-- left input are necessary to account for the pre-join item column
-- shift in the right input.
joinPredicate :: VecItems -> L.JoinPredicate SL.Expr -> [(Expr, Expr, JoinRel)]
joinPredicate (VecItems o) (L.JoinPred conjs) =
    N.toList $ fmap (joinConjunct o) conjs

-- | Translate one component of a conjunctive join predicate into a relational
-- expression. Parameter 'o' specifies the column offset for the relational
-- schema.
joinConjunct :: Int -> L.JoinConjunct SL.Expr -> (Expr, Expr, JoinRel)
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

windowFunction :: SL.WinFun -> WinFun
windowFunction (SL.WinSum e)        = WinSum $ taExpr e
windowFunction (SL.WinMin e)        = WinMin $ taExpr e
windowFunction (SL.WinMax e)        = WinMax $ taExpr e
windowFunction (SL.WinAvg e)        = WinAvg $ taExpr e
windowFunction (SL.WinAll e)        = WinAll $ taExpr e
windowFunction (SL.WinAny e)        = WinAny $ taExpr e
windowFunction (SL.WinFirstValue e) = WinFirstValue $ taExpr e
windowFunction SL.WinCount          = WinCount

frameSpecification :: SL.FrameSpec -> FrameBounds
frameSpecification SL.FAllPreceding   = ClosedFrame FSUnboundPrec FECurrRow
frameSpecification (SL.FNPreceding n) = ClosedFrame (FSValPrec n) FECurrRow

--------------------------------------------------------------------------------

-- | The default value for sums over empty lists for all possible
-- numeric input types.
sumDefault :: T.ScalarType -> (ATy, AVal)
sumDefault T.IntT     = (AInt, int 0)
sumDefault T.DoubleT  = (ADouble, double 0)
sumDefault T.DecimalT = (ADec, dec 0)
sumDefault _          = $impossible

aggrFunDefault :: SL.AggrFun -> Maybe AVal
aggrFunDefault (SL.AggrSum t _)         = Just $ snd $ sumDefault t
aggrFunDefault (SL.AggrAny _)           = Just $ bool False
aggrFunDefault (SL.AggrAll _)           = Just $ bool True
aggrFunDefault (SL.AggrMax _)           = Nothing
aggrFunDefault (SL.AggrMin _)           = Nothing
aggrFunDefault (SL.AggrAvg _)           = Nothing
aggrFunDefault SL.AggrCount             = Nothing
aggrFunDefault (SL.AggrCountDistinct _) = Nothing

groupJoinDefault :: AlgNode
                 -> VecOrder
                 -> VecKey
                 -> VecRef
                 -> VecItems
                 -> [(Attr, Maybe AVal)]
                 -> Build TableAlgebra AlgNode
groupJoinDefault qa o k r i defaultVals =
    proj (vecProj o k r i ++ defaultProj) qa
  where
    defaultProj = [ case mVal of
                        Just val -> eP col (BinAppE Coalesce (ColE col) (ConstE val))
                        Nothing  -> cP col
                  | (col, mVal) <- defaultVals
                  ]

requiresOuterJoin :: SL.AggrFun -> Bool
requiresOuterJoin a = case a of
    SL.AggrSum _ _         -> True
    SL.AggrAny _           -> True
    SL.AggrAll _           -> True
    SL.AggrCount           -> True
    SL.AggrCountDistinct _ -> True
    SL.AggrMax _           -> False
    SL.AggrMin _           -> False
    SL.AggrAvg _           -> False

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

aggrDefault :: AlgNode
            -> VecOrder
            -> VecKey
            -> VecRef
            -> [(Attr, Maybe AVal)]
            -> Build TableAlgebra AlgNode
aggrDefault qa o k r defaultVals =
    proj (vecProj o k r (VecItems 0) ++ defaultProj) qa
  where
    defaultProj = [ case mVal of
                        Just val -> eP col (BinAppE Coalesce (ColE col) (ConstE val))
                        Nothing  -> cP col
                  | (col, mVal) <- defaultVals
                  ]

flipDir :: SortDir -> SortDir
flipDir Asc  = Desc
flipDir Desc = Asc

-- | From an order specification generate a sorting specification from which a
-- synthetic order column can be created.
synthOrder :: VecOrder -> [SortSpec]
synthOrder (VecOrder dirs) = [ (ColE $ oc c, d)| c <- [1..] | d <- dirs ]

--------------------------------------------------------------------------------

-- | The standard identifier value for the unit segment.
unitSegId :: AVal
unitSegId = int 1
