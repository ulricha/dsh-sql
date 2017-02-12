-- FIXME once 7.8 is out, use overloaded list notation for sets
-- instead of S.fromList!
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Backend.Sql.Opt.Properties.Keys where

import           Data.List
import qualified Data.Map                                          as M

import qualified Data.Set.Monad                                    as S

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary
import           Database.DSH.Backend.Sql.Opt.Properties.Types
import           Database.DSH.Common.Impossible

subsetsOfSize :: Ord a => Int -> S.Set a -> S.Set (S.Set a)
subsetsOfSize n s
    | n == 0                    = S.singleton S.empty
    | S.size s < n || n < 0     = error "onlyLists: out of range n"
    | S.size s == n             = S.singleton s
    | otherwise                 = S.fromDistinctAscList . map S.fromDistinctAscList $
                                                         go n (S.size s) (S.toList s)
      where
        go 1 _ xs = map return xs
        go k l (x:xs)
            | k == l = [x:xs]
            | otherwise = map (x:) (go (k-1) (l-1) xs) ++ go k (l-1) xs
        go _ _ [] = $impossible

-- | Enumerate all subsets of size n

-- | Compute keys for rank and rowrank operators
rowRankKeys :: Attr -> S.Set Attr -> Card1 -> S.Set PKey -> S.Set PKey
rowRankKeys resCol sortCols childCard1 childKeys =
    -- All old keys stay intact
    childKeys
    ∪
    -- Trivial case: singleton input
    [ ss resCol | childCard1 ]
    ∪
    -- If sorting columns form a part of a key, the output column
    -- combined with the key columns that are not sorting columns also
    -- is a key.
    [ ss resCol ∪ (k ∖ sortCols)
    | k <- childKeys
    , k ∩ sortCols /= S.empty
    ]

-- | Update a key under a projection. If one attribute is mapped to
-- multiple attributes, the key is replicated.
updateKey :: M.Map Attr (S.Set Attr) -> PKey -> S.Set PKey
updateKey m = go S.empty
  where
    -- FIXME this doesn't look right: keySuffix' unused, go not recursive.
    go :: S.Set PKey -> PKey -> S.Set PKey
    go keyPrefixes keySuffix =
        let (b, keySuffix') = S.deleteFindMin keySuffix
        in case M.lookup b m of
               Nothing -> S.empty
               Just as -> [ S.insert a kp | kp <- keyPrefixes, a <- as ]


inferKeysNullOp :: NullOp -> S.Set PKey
inferKeysNullOp op =
    case op of
        -- FIXME check all combinations of columns for uniqueness
        LitTable (vals, schema)  -> S.fromList
                                    $ map (ss . snd)
                                    $ filter (isKey . fst)
                                    $ zip (transpose vals) (map fst schema)
          where
            isKey :: [AVal] -> Bool
            isKey vs = not $ hasDuplicates $ sort vs

            hasDuplicates :: [AVal] -> Bool
            hasDuplicates (v1:v2:vs) = v1 == v2 || hasDuplicates (v2:vs)
            hasDuplicates _          = False

        TableRef (_, _, keys) -> S.fromList $ map (\(Key k) -> ls k) keys

inferKeysUnOp :: S.Set PKey -> Card1 -> S.Set Attr -> UnOp -> S.Set PKey
inferKeysUnOp childKeys childCard1 childCols op =
    case op of
        WinFun _                       -> childKeys
        RowNum (resCol, _, [])         -> S.insert (ss resCol) childKeys
        -- FIXME can we infer a key here if partitioning includes
        -- general expressions?
        RowNum (resCol, _, pexprs)     -> {- (S.singleton $ ls [resCol, pattr])
                                          ∪ -}
                                          [ ss resCol | childCard1 ]
                                          ∪
                                          childKeys
        -- FIXME infer complete rank keys
        RowRank (resCol, sortInfo)     -> childKeys -- rowRankKeys resCol (ls $ map fst sortInfo) childCard1 childKeys
        Rank (resCol, sortInfo)        -> childKeys -- rowRankKeys resCol (ls $ map fst sortInfo) childCard1 childKeys

        -- This is just the standard Pathfinder way: we take all keys
        -- whose columns survive the projection and update to the new
        -- attr names. We could consider all expressions, but need to
        -- be careful here as not all operators might be injective.
        Project projs           ->
            let m = mapColMulti projs
            in S.foldr (\k ks -> updateKey m k ∪ ks) S.empty childKeys
        Select _                 -> childKeys
        Distinct _               -> S.insert childCols childKeys
        Aggr (_, [])             -> S.empty
        Aggr (_, pexprs@(_ : _)) -> S.singleton $ S.fromList $ map fst pexprs
        Serialize _              -> S.empty

inferKeysBinOp :: S.Set PKey -> S.Set PKey -> Card1 -> Card1 -> BinOp -> S.Set PKey
inferKeysBinOp leftKeys rightKeys leftCard1 rightCard1 op =
    case op of
        Cross _      -> [ k | k <- leftKeys, rightCard1 ]
                        ∪
                        [ k | k <- rightKeys, leftCard1 ]
                        ∪
                        [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]
        ThetaJoin preds -> [ k | k <- leftKeys, rightCard1 ]
                           ∪
                           [ k | k <- rightKeys, leftCard1 ]
                           ∪
                           [ k
                           | k <- leftKeys
                           , (_, be, p) <- S.fromList preds
                           , p == EqJ
                           , b            <- singleCol be
                           , ss b ∈ rightKeys
                           ]
                           ∪
                           [ k
                           | k <- rightKeys
                           , (ae, _, p) <- S.fromList preds
                           , p == EqJ
                           , a            <- singleCol ae
                           , ss a ∈ leftKeys
                           ]
                           ∪
                           [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]

        -- For a left outer join, only consider keys from the
        -- left input. For the right input, columns might end up
        -- containing NULLs which we do not want to deal with here.
        LeftOuterJoin preds -> [ k | k <- leftKeys, rightCard1 ]
                               ∪
                               [ k
                               | k <- leftKeys
                               , (_, be, p) <- S.fromList preds
                               , p == EqJ
                               , b            <- singleCol be
                               , ss b ∈ rightKeys
                               ]

        SemiJoin _    -> leftKeys
        AntiJoin _    -> leftKeys
        DisjUnion _   -> S.empty -- FIXME need domain property.
        Difference _  -> leftKeys

singleCol :: Expr -> S.Set Attr
singleCol (ColE c) = S.singleton c
singleCol _        = S.empty


