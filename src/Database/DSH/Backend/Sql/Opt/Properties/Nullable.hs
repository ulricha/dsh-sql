{-# LANGUAGE MonadComprehensions #-}

module Database.DSH.Backend.Sql.Opt.Properties.Nullable
    ( inferNullableNullOp
    , inferNullableUnOp
    , inferNullableBinOp
    ) where

import qualified Data.Set.Monad as S

import Database.Algebra.Table.Lang


import Database.DSH.Backend.Sql.Opt.Properties.Types
import Database.DSH.Backend.Sql.Opt.Properties.Auxiliary

nullableExpr :: S.Set Attr -> Expr -> Bool
nullableExpr ns e =
    case e of
        BinAppE Coalesce e1 e2 -> (nullableExpr ns e1 && nullableExpr ns e2)
                                  ||
                                  (not (nullableExpr ns e1) && nullableExpr ns e2)
        BinAppE _ e1 e2        -> nullableExpr ns e1 || nullableExpr ns e2
        UnAppE _ e1            -> nullableExpr ns e1
        ColE c                 -> c `S.member` ns
        TernaryAppE _ e1 e2 e3 -> any (nullableExpr ns) [e1, e2, e3]
        ConstE _               -> False

nullableAggr :: S.Set Attr -> AggrType -> Bool
nullableAggr ns a =
    case a of
        CountStar       -> False
        Count _         -> False
        CountDistinct _ -> False
        Avg e           -> nullableExpr ns e
        Max e           -> nullableExpr ns e
        Min e           -> nullableExpr ns e
        Sum e           -> nullableExpr ns e
        All e           -> nullableExpr ns e
        Any e           -> nullableExpr ns e

inferNullableNullOp :: NullOp -> S.Set Attr
inferNullableNullOp op =
    case op of
        LitTable _ -> S.empty
        TableRef _ -> S.empty

inferNullableUnOp :: S.Set Attr -> UnOp -> S.Set Attr
inferNullableUnOp ns op =
    case op of
        Serialize _      -> ns
        Select _         -> ns
        Distinct _       -> ns
        Project ps       -> ls [ a | (a, e) <- ps, nullableExpr ns e ]
        RowNum (c, _, _) -> S.delete c ns
        RowRank (c, _)   -> S.delete c ns
        Rank (c, _)      -> S.delete c ns
        -- Non-grouped aggregate functions might return NULL if their
        -- input is empty (except for COUNT)
        Aggr (as, [])    -> ns ∪ ls [ c | (a, c) <- as, nullableAggr ns a ]
        -- For grouped aggregates:
        -- 1. The grouping columns might be NULL if they were nullable in the input.
        --
        -- 2. Aggregate output (except for COUNT) is nullable if the
        -- input expression is nullable
        Aggr (as, gs)    -> ls [ c | (c, e) <- gs, nullableExpr ns e ]
                            ∪
                            ls [ c | (a, c) <- as, nullableAggr ns a ]
        -- FIXME under what circumstances does the window aggregate
        -- output get NULL? This is the safe variant that considers
        -- the output always nullable.
        WinFun a         -> let ((c, _), _, _, _) = a in S.insert c ns

inferNullableBinOp :: BottomUpProps -> BottomUpProps -> BinOp -> S.Set Attr
inferNullableBinOp ps1 ps2 op =
    case op of
        Cross _         -> pNullable ps1 ∪ pNullable ps2
        -- FIXME for joins we could be more precise: any column that
        -- shows up in the join predicate can be considered non-null
        -- in the join result (tuples in which the predicate evaluates
        -- to NULL will not be in the result).
        EqJoin _        -> pNullable ps1 ∪ pNullable ps2
        ThetaJoin _     -> pNullable ps1 ∪ pNullable ps2
        LeftOuterJoin _ -> pNullable ps1 ∪ [ c | (c, _) <- pCols ps2 ]
        SemiJoin _      -> pNullable ps1
        AntiJoin _      -> pNullable ps1
        DisjUnion _     -> pNullable ps1 ∪ pNullable ps2
        Difference _    -> pNullable ps1
