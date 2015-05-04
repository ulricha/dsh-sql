{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Infer functional dependencies from table algebra operators.
module Database.DSH.Backend.Sql.Opt.Properties.FD
    ( inferFDNullOp
    , inferFDUnOp
    , inferFDBinOp
    ) where

import qualified Data.Set.Monad                                    as S
import           Data.Tuple
import           Data.Maybe

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary
import           Database.DSH.Backend.Sql.Opt.Properties.Types
import           Database.DSH.Common.Impossible

inferFDNullOp :: S.Set TypedAttr -> S.Set PKey -> NullOp -> S.Set FD
inferFDNullOp cs ks op =
    case op of
        LitTable _ -> [ FD k c | k <- ks, (c, _) <- cs, k /= ss c ]
        TableRef _ -> [ FD k c | k <- ks, (c, _) <- cs, k /= ss c ]

updateSet :: [(Attr, Attr)] -> S.Set Attr -> Maybe (S.Set Attr)
updateSet colMap cs =
    S.foldr' (\c mcs -> S.insert <$> lookup c colMap <*> mcs)
             (Just S.empty)
             cs

updateFD :: [(Attr, Attr)] -> FD -> S.Set FD
updateFD colMap (FD scs dc) = maybe S.empty id $ do
    scs' <- updateSet colMap scs
    dc'  <- lookup dc colMap
    return $ ss $ FD scs' dc'

inferFDUnOp :: BottomUpProps -> UnOp -> S.Set FD
inferFDUnOp p op =
    case op of
        Distinct _ -> pFunDeps p
        Select _  -> pFunDeps p
        RowNum (r, _, []) -> pFunDeps p ∪ [ FD (ss r) c | (c, _) <- pCols p ]
        -- FIXME the combination of sorting and grouping cols propably
        -- determines r.
        RowNum (_, _, _) -> pFunDeps p
        -- FIXME dependency r -> sortcols
        RowRank _ -> pFunDeps p
        Aggr (_, []) -> S.empty
        Aggr (as, gs) -> ls [ FD (ls $ map fst gs) c | (_, c) <- as ]
        Project ps ->
            let colMap = S.toList $ S.map swap $ S.fromList $ mapMaybe mapCol ps
            in unionss $ fmap (updateFD colMap) (pFunDeps p)
        Serialize _ -> pFunDeps p
        WinFun _ -> $unimplemented
        Rank _ -> $unimplemented

inferFDBinOp :: BottomUpProps   -- ^ Properties of the left child
             -> BottomUpProps   -- ^ Properties of the right child
             -> S.Set PKey      -- ^ The keys of the operator itself
             -> S.Set TypedAttr -- ^ The cols of the operator itself
             -> BinOp           -- ^ The operator
             -> S.Set FD
inferFDBinOp p1 p2 ks cs op =
    case op of
        Cross _ ->
            pFunDeps p1 ∪ pFunDeps p2
            ∪
            [ FD k c | k <- ks, (c, _) <- cs, k /= ss c ]
        ThetaJoin _ ->
            pFunDeps p1 ∪ pFunDeps p2
            ∪
            [ FD k c | k <- ks, (c, _) <- cs, k /= ss c ]
        SemiJoin _ -> pFunDeps p1
        AntiJoin _ -> pFunDeps p1
        LeftOuterJoin _ -> pFunDeps p1
        DisjUnion _ -> S.empty
        Difference _ -> pFunDeps p1
        EqJoin _ -> $unimplemented
