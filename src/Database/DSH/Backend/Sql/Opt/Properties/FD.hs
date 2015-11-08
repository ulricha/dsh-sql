{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Infer functional dependencies from table algebra operators.
module Database.DSH.Backend.Sql.Opt.Properties.FD
    ( inferFDNullOp
    , inferFDUnOp
    , inferFDBinOp
    ) where

import qualified Data.Map                                          as M
import           Data.Maybe
import qualified Data.Set.Monad                                    as S
import           Data.Tuple

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary
import           Database.DSH.Backend.Sql.Opt.Properties.Types
import           Database.DSH.Common.Impossible

inferFDNullOp :: S.Set TypedAttr -> S.Set PKey -> NullOp -> FDSet
inferFDNullOp tcs ks op =
    case op of
        LitTable _ -> FDSet $ foldr (\k m -> M.insert k (cs S.\\ k) m) M.empty ks
        TableRef _ -> FDSet $ foldr (\k m -> M.insert k (cs S.\\ k) m) M.empty ks

  where
    cs = fmap fst tcs

-- | Update an attribute set with new names. All attributes must find
-- a new name.
updateSetAll :: [(Attr, Attr)] -> S.Set Attr -> Maybe (S.Set Attr)
updateSetAll colMap cs =
    S.foldr' (\c mcs -> S.insert <$> lookup c colMap <*> mcs)
             (Just S.empty)
             cs

-- | Update an attribute set with new names. Attributes for which no
-- new name exists are removed.
updateSet :: [(Attr, Attr)] -> S.Set Attr -> S.Set Attr
updateSet colMap cs = unionss $ fmap (\c -> maybe S.empty ss $ lookup c colMap) cs

updateFD :: [(Attr, Attr)] -> S.Set Attr -> S.Set Attr -> FDSet -> FDSet
updateFD colMap dets deps (FDSet m) =
    case (updateSetAll colMap dets, updateSet colMap deps) of
        (Just dets', deps') | deps' /= S.empty -> FDSet $ M.insert dets' deps' m
        _                                      -> FDSet m

-- | Update a set of functional dependencies with new names from a
-- projection. A functional dependency is kept if all attributes from
-- the determinant set can be mapped and if at least one attribute
-- from the dependent set can be mapped.
updateFDSet :: [(Attr, Attr)] -> FDSet -> FDSet
updateFDSet colMap (FDSet m) = M.foldrWithKey (updateFD colMap) emptyFDSet m

-- -- | Add a functional dependency for a single attribute to a set of FDs.
-- addFunDep :: S.Set Attr -> Attr -> FDSet -> FDSet
-- addFunDep cs c (FDSet m) = FDSet $ M.insertWith S.union cs (ss c) m

-- | Add a dependency for a set of attributes to a set of FDs.
addFunDeps :: S.Set Attr -> S.Set Attr -> FDSet -> FDSet
addFunDeps cs cs' (FDSet m) = FDSet $ M.insertWith S.union cs cs' m

cols :: BottomUpProps -> S.Set Attr
cols p = fmap fst $ pCols p

inferFDUnOp :: BottomUpProps -> UnOp -> FDSet
inferFDUnOp p op =
    case op of
        Distinct _ -> pFunDeps p
        Select _  -> pFunDeps p
        RowNum (r, _, []) -> addFunDeps (ss r) (cols p) (pFunDeps p)
        -- FIXME the combination of sorting and grouping cols propably
        -- determines r.
        RowNum (_, _, _) -> pFunDeps p
        -- FIXME dependency r -> sortcols
        RowRank _ -> pFunDeps p
        Aggr (_, []) -> emptyFDSet
        -- Dependencies among grouping columns stay intact and are
        -- updated in the same way as for projections.
        Aggr (as, gs) ->
            let colMap = S.toList $ S.map swap $ S.fromList $ mapMaybe mapCol gs
            in addFunDeps (ls $ map fst gs)
                          (S.fromList $ map snd as)
                          (updateFDSet colMap (pFunDeps p))
        Project ps ->
            let colMap = S.toList $ S.map swap $ S.fromList $ mapMaybe mapCol ps
            in updateFDSet colMap (pFunDeps p)
        Serialize _ -> pFunDeps p
        -- FIXME add FDs for the new columns.
        WinFun _ -> pFunDeps p
        Rank _ -> $unimplemented

inferFDBinOp :: BottomUpProps   -- ^ Properties of the left child
             -> BottomUpProps   -- ^ Properties of the right child
             -> S.Set PKey      -- ^ The keys of the operator itself
             -> S.Set TypedAttr -- ^ The cols of the operator itself
             -> BinOp           -- ^ The operator
             -> FDSet
inferFDBinOp p1 p2 ks cs op =
    case op of
        -- Determine functional dependency of a cartesian
        -- product. Note: As we know that attribute sets of left and
        -- right inputs are disjunct, we don't have to care for
        -- collisions in the functional dependencies during unioning.
        Cross _ -> FDSet $
            -- Dependencies from either side are still valid after the product
            (fdsRep $ pFunDeps p1)
            `M.union`
            (fdsRep $ pFunDeps p2)
            `M.union`
            -- The new combined keys determine all result columns of the product.
            (foldr (\k m -> M.insert k ((fmap fst cs) S.\\ k) m) M.empty ks)
        ThetaJoin _ -> FDSet $
            (fdsRep $ pFunDeps p1)
            `M.union`
            (fdsRep $ pFunDeps p2)
            `M.union`
            (foldr (\k m -> M.insert k ((fmap fst cs) S.\\ k) m) M.empty ks)
        SemiJoin _ -> pFunDeps p1
        AntiJoin _ -> pFunDeps p1
        LeftOuterJoin _ -> pFunDeps p1
        DisjUnion _ -> emptyFDSet
        Difference _ -> pFunDeps p1
        EqJoin _ -> $unimplemented
