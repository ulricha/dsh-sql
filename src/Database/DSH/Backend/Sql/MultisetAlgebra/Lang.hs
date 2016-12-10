{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.Lang
    ( MA
    , NullaryOp(..)
    , UnOp(..)
    , BinOp(..)
    , project, select, distinct, groupAggr, rownum, rownumPart
    , cartProduct, thetaJoin, semiJoin, antiJoin, union
    , leftOuterJoin, groupJoin
    , lit, tableRef
    ) where

import           Data.Aeson.TH

import qualified Data.Sequence                  as S

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import qualified Database.DSH.Common.VectorLang as VL

-- FIXME add keys
data NullaryOp = Lit (VL.PType, S.Seq VL.TExpr)
               | Table (String, VL.PType, L.BaseTableSchema)
               deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullaryOp)

data UnOp = Project VL.TExpr
          | Select VL.TExpr
          | Distinct ()
          | GroupAggr (VL.TExpr, L.NE (VL.AggrFun VL.TExpr))
          | RowNumPart (VL.TExpr, VL.TExpr)
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = CartProduct ()
           | ThetaJoin (L.JoinPredicate VL.TExpr)
           | SemiJoin (L.JoinPredicate VL.TExpr)
           | AntiJoin (L.JoinPredicate VL.TExpr)
           | LeftOuterJoin (L.JoinPredicate VL.TExpr, VL.TExpr, VL.TExpr)
           | GroupJoin (L.JoinPredicate VL.TExpr, L.NE (VL.AggrFun VL.TExpr))
           | Union ()
           deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

-- | Multiset Algebra
type MA = Algebra () BinOp UnOp NullaryOp AlgNode

--------------------------------------------------------------------------------
-- Constructors in the 'Build' monad

project :: VL.TExpr -> AlgNode -> Build MA AlgNode
project e n = insert (UnOp (Project e) n)

select :: VL.TExpr -> AlgNode -> Build MA AlgNode
select e n = insert (UnOp (Select e) n)

distinct :: AlgNode -> Build MA AlgNode
distinct n = insert (UnOp (Distinct ()) n)

groupAggr :: VL.TExpr -> L.NE (VL.AggrFun VL.TExpr) -> AlgNode -> Build MA AlgNode
groupAggr e as n = insert (UnOp (GroupAggr (e, as)) n)

rownumPart :: VL.TExpr -> VL.TExpr -> AlgNode -> Build MA AlgNode
rownumPart g o n = insert (UnOp (RowNumPart (g, o)) n)

rownum :: VL.TExpr -> AlgNode -> Build MA AlgNode
rownum o n = insert (UnOp (RowNumPart (VL.TConstant L.UnitV, o)) n)

semiJoin :: (L.JoinPredicate VL.TExpr) -> AlgNode -> AlgNode -> Build MA AlgNode
semiJoin p n1 n2 = insert (BinOp (SemiJoin p) n1 n2)

antiJoin :: (L.JoinPredicate VL.TExpr) -> AlgNode -> AlgNode -> Build MA AlgNode
antiJoin p n1 n2 = insert (BinOp (AntiJoin p) n1 n2)

thetaJoin :: (L.JoinPredicate VL.TExpr) -> AlgNode -> AlgNode -> Build MA AlgNode
thetaJoin p n1 n2 = insert (BinOp (ThetaJoin p) n1 n2)

leftOuterJoin :: (L.JoinPredicate VL.TExpr) -> VL.TExpr -> VL.TExpr -> AlgNode -> AlgNode -> Build MA AlgNode
leftOuterJoin p d r n1 n2 = insert (BinOp (LeftOuterJoin (p, d, r)) n1 n2)

groupJoin :: (L.JoinPredicate VL.TExpr) -> L.NE (VL.AggrFun VL.TExpr) -> AlgNode -> AlgNode -> Build MA AlgNode
groupJoin p as n1 n2 = insert (BinOp (GroupJoin (p, as)) n1 n2)

cartProduct :: AlgNode -> AlgNode -> Build MA AlgNode
cartProduct n1 n2 = insert (BinOp (CartProduct ()) n1 n2)

union :: AlgNode -> AlgNode -> Build MA AlgNode
union n1 n2 = insert (BinOp (Union ()) n1 n2)

lit :: VL.PType -> S.Seq VL.TExpr -> Build MA AlgNode
lit ty vs = insert (NullaryOp (Lit (ty, vs)))

tableRef :: String -> VL.PType -> L.BaseTableSchema -> Build MA AlgNode
tableRef n t s = insert (NullaryOp (Table (n, t, s)))
