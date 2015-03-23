{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

-- | Implementation of vector primitives in terms of table algebra
-- operators.
module Database.DSH.Backend.Sql.VectorAlgebra () where

-- import           Control.Applicative              hiding (Const)
import           Data.List.NonEmpty               (NonEmpty)
import qualified Data.List.NonEmpty               as N
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
ordProj (VecOrder ds) = zipWith (\_ i -> cP (oc i)) (N.toList ds) [1..]

itemProj :: VecItems -> [Proj]
itemProj (VecItems (Just i)) = map (cP . ic) [1..i]
itemProj (VecItems Nothing)  = []

refProj :: VecRef -> [Proj]
refProj (VecRef (Just i)) = map (cP . ic) [1..i]
refProj (VecRef Nothing)  = []

-- | Create the relational representation of a transformation vector
-- from a single data vector. The key is duplicated into source and
-- destination columns.
transProj :: VecKey -> [Proj]
transProj (VecKey i) = [ mP (sc c) (kc c) | c <- [1..i] ]
                       ++
                       [ mP (dc c) (kc c) | c <- [1..i] ]

vecTopProj :: VecOrder -> VecKey -> VecRef -> VecItems -> [Proj]
vecTopProj order key ref items = ordProj order
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


-- projAddCols :: [VL.DBCol] -> [Proj] -> AlgNode -> Build TableAlgebra AlgNode
-- projAddCols cols projs q = proj ([cP descr, cP pos] ++ map (cP . itemi) cols ++ projs) q

-- itemProj :: [VL.DBCol] -> [Proj] -> [Proj]
-- itemProj cols projs = projs ++ [ cP $ itemi i | i <- cols ]


aggrFun :: VL.AggrFun -> AggrType
aggrFun (VL.AggrSum _ e) = Sum $ taExpr e
aggrFun (VL.AggrMin e)   = Min $ taExpr e
aggrFun (VL.AggrMax e)   = Max $ taExpr e
aggrFun (VL.AggrAvg e)   = Avg $ taExpr e
aggrFun (VL.AggrAll e)   = All $ taExpr e
aggrFun (VL.AggrAny e)   = Any $ taExpr e
aggrFun VL.AggrCount     = Count

joinPredicate :: Int -> L.JoinPredicate VL.Expr -> [(Expr, Expr, JoinRel)]
joinPredicate o (L.JoinPred conjs) = N.toList $ fmap joinConjunct conjs
  where
    joinConjunct :: L.JoinConjunct VL.Expr -> (Expr, Expr, JoinRel)
    joinConjunct (L.JoinConjunct e1 op e2) = (taExpr e1, taExprOffset o e2, joinOp op)

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

    vecSelect expr (TADVec q o (VecKey k) r i) = do
        qs <- select (taExpr expr) q
        qr <- proj (transProj (VecKey k)) q
        return ( TADVec qs o (VecKey k) r i
               , TARVec qr (VecTransSrc k) (VecTransDst k)
               )

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

        items = VecItems $ Just $ N.length $ L.tableCols schema
        order = VecOrder $ fmap (const Asc) baseKeyCols
        key   = VecKey $ N.length baseKeyCols
        ref   = VecRef Nothing
