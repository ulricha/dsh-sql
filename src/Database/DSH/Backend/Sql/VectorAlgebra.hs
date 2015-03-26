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

gc :: Int -> Attr
gc i = "g" ++ show i

keyCols :: VecKey -> [Attr]
keyCols (VecKey i) = [ kc c | c <- [1..i] ]

ordCols :: VecOrder -> [Attr]
ordCols (VecOrder o) = [ oc c | c <- [1..] | _ <- o ]

refCols :: VecRef -> [Attr]
refCols (VecRef i) = [ rc c | c <- [1..i] ]

itemCols :: VecItems -> [Attr]
itemCols (VecItems i) = [ ic c | c <- [1..i] ]

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

srcProj :: VecTransSrc -> [Proj]
srcProj (VecTransSrc i) = map (cP . sc) [1..i]

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

keyRefProj :: VecKey -> [Proj]
keyRefProj (VecKey i) = [ mP (rc c) (kc c) | c <- [1..i] ]

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
          (proj (refProj r ++ itemProj (VecItems 1)) qa)
           `unionM`
           projM (refProj r ++ [eP (ic 1) (ConstE defaultValue)])
               -- We know that the outer key must be aligned with inner references.
               (differenceM
                   (proj (keyRefProj ok) qo)
                   (proj (refProj r) qa))

--------------------------------------------------------------------------------

-- | The VectorAlgebra instance for TA algebra, implemented using
-- natural keys.
instance VL.VectorAlgebra TableAlgebra where
    type DVec TableAlgebra = TADVec
    type PVec TableAlgebra = TAPVec
    type RVec TableAlgebra = TARVec

    vecNumber (TADVec q o k r i) = do
        let i' = VecItems (unItems i + 1)

            nc = ic (unItems i + 1)

        qn <- rownum nc (ordCols o) [] q

        return $ TADVec qn o k r i'

    vecSort sortExprs (TADVec q o k r i) = do
        let o'       = VecOrder (map (const Asc) sortExprs) <> o
            -- Include the old order columns. This implements stable
            -- sorting and guarantees a strict total order of columns.
            sortCols = [ eP (oc c) (taExpr e) | c <- [1..] | e <- sortExprs ]
                       ++
                       [ mP (oc (c + length sortExprs)) (oc c)
                       | c <- [1..unOrd o]
                       ]
            srcCols  = [ mP (sc c) (oc c) | c <- [1..unOrd o] ]
            s        = VecTransSrc (unOrd o)
            d        = VecTransDst (unOrd o')

        qe <- proj (sortCols ++ keyProj k ++ refProj r ++ itemProj i ++ srcCols) q
        qs <- proj (vecProj o' k r i) qe
        -- qp <- proj (srcProj s ++ [ mP (dc c) (oc c) | c <- [1..unOrd o'] ]) qe
        qp <- undefined
        return ( TADVec qs o' k r i
               , TAPVec qp s d
               )

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


    vecNestJoin p v1@(TADVec q1 o1 k1 _ i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = keyRef k1  -- nesting operator: left key defines reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (ordProj o ++ keyProj k ++ keyRefProj k1 ++ itemProj i)
               $ thetaJoinM (joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TAPVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TAPVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
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

        qa  <- projM (ordProj o ++ keyProj k ++ refProj r1 ++ itemProj i)
               $ aggrM [(aggrFun a, acol)] groupCols
               $ leftOuterJoinM (joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qd <- case a of
                  VL.AggrSum t _ -> groupJoinDefault qa o k r i1 (snd $ sumDefault t)
                  VL.AggrAny _   -> groupJoinDefault qa o k r i1 (bool False)
                  VL.AggrAll _   -> groupJoinDefault qa o k r i1 (bool True)
                  VL.AggrCount   -> groupJoinDefault qa o k r i1 (int 0)
                  -- FIXME this is a hack to simulate the (incorrect)
                  -- behaviour of regular NestJoin + AggrS when empty
                  -- groups occur for non-defaulting
                  -- aggregates. Whereas the Align join for AggrS
                  -- removes (outer) tuples with empty groups
                  -- implicitly, we do this explicitly here.
                  _              -> select (UnAppE Not (UnAppE IsNull (ColE acol)))
                                           qa

        return $ TADVec qd o k r i

    vecAggrS a (TADVec qo _ k1 _ _) (TADVec qi _ _ r2 _) = do
        -- Group the inner vector by ref.
        qa <- aggr [(aggrFun a, ic 1)] [ (c, ColE c) | c <- refCols r2 ] qi
        qd <- case a of
                  VL.AggrSum t _ -> segAggrDefault qo qa k1 r2 (snd $ sumDefault t)
                  VL.AggrAny _   -> segAggrDefault qo qa k1 r2 (bool False)
                  VL.AggrAll _   -> segAggrDefault qo qa k1 r2 (bool True)
                  VL.AggrCount   -> segAggrDefault qo qa k1 r2 (int 0)
                  _              -> return qa

        return $ TADVec qd (VecOrder [Asc]) (VecKey 1) r2 (VecItems 1)

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

    vecGroup groupExprs (TADVec q o k r i) = do
        let gl = length groupExprs
        let o1 = VecOrder (map (const Asc) groupExprs)
            k1 = VecKey gl
            r1 = VecRef 0
            i1 = VecItems gl

        let o2 = VecOrder (replicate (gl + unOrd o) Asc)
            k2 = k
            r2 = VecRef gl
            i2 = i

        -- Apply the grouping expressions
        let groupCols  = [ gc (c + unItems i) | c <- [1..] | _ <- groupExprs ]
            groupProj  = [ eP g (taExpr ge) | g <- groupCols | ge <- groupExprs ]

        qg <- proj (vecProj o k r i ++ groupProj) q

        -- Generate the outer vector: one tuple per distinct values of
        -- the grouping columns.
        let outerKeyProj = [ mP (kc c) g | c <- [1..] | g <- groupCols ]
            outerOrdProj = [ mP (oc c) g | c <- [1..] | g <- groupCols ]
            outerItemProj = [ mP (ic c) g | c <- [1..] | g <- groupCols ]

        qo <- projM (outerOrdProj ++ outerKeyProj ++ outerItemProj)
              $ distinctM
              $ proj [ cP g | g <- groupCols ] qg

        -- Generate the inner vector that references the groups in the
        -- outer vector.
        let innerRefProj = [ mP (rc c) g | c <- [1..] | g <- groupCols ]
            innerOrdProj = [ mP (oc c) go
                           | c <- [1..]
                           | go <- groupCols ++ ordCols o
                           ]

        qi <- proj (innerOrdProj ++ keyProj k ++ innerRefProj ++ itemProj i) q

        -- Generate the propagation vector
        qp <- undefined

        return ( TADVec qo o1 k1 r1 i1
               , TADVec qi o2 k2 r2 i2
               , TAPVec qp undefined undefined
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
        order = VecOrder $ fmap (const Asc) $ N.toList baseKeyCols
        key   = VecKey $ N.length baseKeyCols
        ref   = VecRef 0
