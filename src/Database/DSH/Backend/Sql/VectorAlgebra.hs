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

-- import           Control.Applicative              hiding (Const)
import           Control.Exception.Base
import           Data.List.NonEmpty               (NonEmpty)
import qualified Data.List.NonEmpty               as N
import           Data.Monoid                      hiding (Sum, Any, All)
import           GHC.Exts

-- import           Database.Algebra.Dag.Build
-- import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Construct
import           Database.Algebra.Table.Lang

import qualified Database.DSH.Common.Lang         as L
import qualified Database.DSH.Common.Type         as T

import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Common.Impossible
import qualified Database.DSH.VL                  as VL

--------------------------------------------------------------------------------
-- Column names

ic :: Int -> Attr
ic i = "i" ++ show i

kc :: Int -> Attr
kc i = "k" ++ show i

oc :: Int -> Attr
oc i = "o" ++ show i

rc :: Int -> Attr
rc i = "r" ++ show i

sc :: Int -> Attr
sc i = "s" ++ show i

dc :: Int -> Attr
dc i = "d" ++ show i

--------------------------------------------------------------------------------
-- Projection

cP :: Attr -> Proj
cP a = (a, ColE a)

eP :: Attr -> Expr -> Proj
eP = (,)

mP :: Attr -> Attr -> Proj
mP n o = (n, ColE o)

keyProj :: VecKey -> [Proj]
keyProj (VecKey i) = map (cP . kc) $ [1..i]

ordProj :: VecOrder -> [Proj]
ordProj (VecOrder ds) = zipWith (\_ i -> cP (oc i)) ds [1..]

refProj :: VecRef -> [Proj]
refProj (VecRef 0) = []
refProj (VecRef i) = map (cP . ic) [1..i]

itemProj :: VecItems -> [Proj]
itemProj (VecItems 0) = []
itemProj (VecItems i) = map (cP . ic) [1..i]

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
keyJoin (VecKey k1) (VecKey k2) = assert (k1 == k2) $
    [ (ColE (kc c), ColE (kc (c + k1)), EqJ) | c <- [1..k1]]




-- | Create the relational representation of a transformation vector
-- from a single data vector. The key is duplicated into source and
-- destination columns.
transProj :: VecKey -> [Proj]
transProj (VecKey i) = [ mP (sc c) (kc c) | c <- [1..i] ]
                       ++
                       [ mP (dc c) (kc c) | c <- [1..i] ]

-- | Generate the left propagation vector for a product-like operator.
prodTransProjLeft :: VecKey -> VecKey -> [Proj]
prodTransProjLeft k1 k2 =
    [ mP (sc c) (kc c) | c <- [1..unKey k1] ]
    ++
    [ mP (dc c) (kc c) | c <- [1..unKey (k1 <> k2)] ]

-- | Generate the right propagation vector for a product-like operator.
prodTransProjRight :: VecKey -> VecKey -> [Proj]
prodTransProjRight k1 k2 =
    [ mP (sc c) (kc c) | c <- [unKey k1 + 1..unKey k1 + unKey k2] ]
    ++
    [ mP (dc c) (kc c) | c <- [1..unKey (k1 <> k2)] ]

-- | Generate a projection that keeps all required columns of a vector
vecProj :: VecOrder -> VecKey -> VecRef -> VecItems -> [Proj]
vecProj order key ref items = ordProj order
                              ++ keyProj key
                              ++ refProj ref
                              ++ itemProj items

chooseBaseKey :: N.NonEmpty L.Key -> NonEmpty Attr
chooseBaseKey keys = case sortWith (\(L.Key k) -> N.length k) $ N.toList keys of
    L.Key k : _ -> fmap (\(L.ColName c) -> c) k
    _           -> $impossible

--------------------------------------------------------------------------------
-- Expressions

algVal :: L.ScalarVal -> AVal
algVal (L.IntV i)     = int (fromIntegral i)
algVal (L.BoolV t)    = bool t
algVal L.UnitV        = int (-1)
algVal (L.StringV s)  = string s
algVal (L.DoubleV d)  = double d
algVal (L.DateV d)    = date d
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
binOp (L.SBDateOp L.AddDays)  = \e1 e2 -> BinAppE Plus e2 e1
binOp (L.SBDateOp L.SubDays)  = \e1 e2 -> BinAppE Minus e2 e1
binOp (L.SBDateOp L.DiffDays) = \e1 e2 -> BinAppE Minus e2 e1

unOp :: L.ScalarUnOp -> UnFun
unOp (L.SUBoolOp L.Not)             = Not
unOp (L.SUCastOp (L.CastDouble))    = Cast doubleT
unOp (L.SUCastOp (L.CastDecimal))   = Cast decT
unOp (L.SUNumOp L.Sin)              = Sin
unOp (L.SUNumOp L.Cos)              = Cos
unOp (L.SUNumOp L.Tan)              = Tan
unOp (L.SUNumOp L.ASin)             = ASin
unOp (L.SUNumOp L.ACos)             = ACos
unOp (L.SUNumOp L.ATan)             = ATan
unOp (L.SUNumOp L.Sqrt)             = Sqrt
unOp (L.SUNumOp L.Exp)              = Exp
unOp (L.SUNumOp L.Log)              = Log
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
aggrFun VL.AggrCount     = Count

-- | Transform a VL join predicate into a TA predicate. Items of the
-- left input are necessary to account for the pre-join item column
-- shift in the right input.
joinPredicate :: VecItems -> L.JoinPredicate VL.Expr -> [(Expr, Expr, JoinRel)]
joinPredicate (VecItems o) (L.JoinPred conjs) =
    N.toList $ fmap (joinConjunct o) conjs

joinConjunct :: Int -> L.JoinConjunct VL.Expr -> (Expr, Expr, JoinRel)
joinConjunct o (L.JoinConjunct e1 op e2) = (taExpr e1, taExprOffset o e2, joinOp op)

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

-- | The VectorAlgebra instance for TA algebra, implemented using
-- natural keys.
instance VL.VectorAlgebra TableAlgebra where
    type DVec TableAlgebra = TADVec
    type PVec TableAlgebra = TAPVec
    type RVec TableAlgebra = TARVec

    vecThetaJoin p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = r1         -- The left vector defines the reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (vecProj o k r i)
               $ thetaJoinM (joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TAPVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TAPVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecAlign (TADVec q1 o1 k1 r1 i1) (TADVec q2 _ k2 _ i2) = do
        -- Join both vectors by their keys. Because this is a
        -- 1:1-join, we can discard order and ref of the right input.
        qa <- projM (ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj (i1 <> i2))
              $ thetaJoinM (keyJoin k1 k2)
                    (return q1)
                    (proj (shiftKey k1 k2 ++ shiftItems i1 i2) q2)
        return $ TADVec qa o1 k1 r1 (i1 <> i2)

    vecSelect expr (TADVec q o (VecKey k) r i) = do
        qs <- select (taExpr expr) q
        qr <- proj (transProj (VecKey k)) q
        return ( TADVec qs o (VecKey k) r i
               , TARVec qr (VecTransSrc k) (VecTransDst k)
               )

    vecProject exprs (TADVec q o k r i) = do
        let projs = zipWith (\c e -> eP (ic c) (taExpr e)) [1..] exprs
        qp <- proj projs q
        return $ TADVec qp o k r i

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
        baseItemProj = [ mP (ic i) c | i <- [1..] | c <- N.toList baseKeyCols ]

        items = VecItems $ N.length $ L.tableCols schema
        order = VecOrder $ fmap (const Asc) $ N.toList baseKeyCols
        key   = VecKey $ N.length baseKeyCols
        ref   = VecRef 0
