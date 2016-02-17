{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Backend.Sql.Opt.Rewrite.Basic where

import           Debug.Trace
import           Text.Printf

import           Control.Arrow
import           Control.Monad
import           Data.Either
-- import           Data.Either.Combinators
import           Data.List                                         hiding
                                                                    (insert)
import qualified Data.Map                                          as M
import           Data.Maybe
import qualified Data.Set.Monad                                    as S

import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang                       hiding
                                                                    (replace)

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary
import           Database.DSH.Backend.Sql.Opt.Properties.Const
import           Database.DSH.Backend.Sql.Opt.Properties.Types
import           Database.DSH.Backend.Sql.Opt.Rewrite.Common
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Opt

cleanup :: TARewrite Bool
cleanup = iteratively $ sequenceRewrites [ applyToAll noProps cleanupRules
                                         , applyToAll inferAll cleanupRulesTopDown
                                         ]

cleanupRules :: TARuleSet ()
cleanupRules = [ stackedProject
               -- , serializeProject
               , pullProjectWinFun
               , pullProjectSelect
               , pullProjectSerialize
               , pullProjectRownum
               , pullProjectAggr
               , pullProjectSemiJoinLeft
               , pullProjectSemiJoinRight
               -- , inlineProjectAggr
               , duplicateSortingCriteriaWin
               , duplicateSortingCriteriaRownum
               -- , duplicateSortingCriteriaSerialize
               , bypassRownumProject
               , pruneSerializeSortCols
               ]

cleanupRulesTopDown :: TARuleSet AllProps
cleanupRulesTopDown = [ unreferencedBaseTableCols
                      , unreferencedRownum
                      , unreferencedRank
                      , unreferencedProjectCols
                      , unreferencedAggrCols
                      , unreferencedLiteralCols
                      , unreferencedGroupingCols
                      , pruneSerializeSortColsFD
                      , inlineSortColsRownum
                      -- , inlineSortColsSerialize
                      , inlineSortColsWinFun
                      , keyPrefixOrdering
                      , constJoinPred
                      , constAggrKey
                      , constRownumCol
                      , constRowRankCol
                      -- , constSerializeCol
                      , constWinOrderCol
                      , pullProjectThetaJoinLeft
                      , pullProjectThetaJoinRight
                      , pullProjectCrossLeft
                      , pullProjectCrossRight
                      , singletonProductLeft
                      , singletonProductRight
                      ]

----------------------------------------------------------------------------------
-- Rewrite rules


---------------------------------------------------------------------------
-- ICols rewrites

unreferencedBaseTableCols :: TARule AllProps
unreferencedBaseTableCols q =
  $(dagPatMatch 'q "TableRef args "
    [| do
        let (n, schema, keys) = $(v "args")
        reqCols <- pICols . td <$> properties q
        let schema' = filter (\(c, _) -> S.member c reqCols) schema

        predicate $ length schema' < length schema

        return $ do
            logRewrite "Basic.ICols.Table" q
            let keys' = filter (\(Key k) -> all (`S.member` reqCols) k)
                               keys
            void $ replaceWithNew q $ NullaryOp $ TableRef (n, schema', keys') |])

-- | Prune a rownumber operator if its output is not required
unreferencedRownum :: TARule AllProps
unreferencedRownum q =
  $(dagPatMatch 'q "RowNum args (q1)"
    [| do
         (res, _, _) <- return $(v "args")
         neededCols  <- pICols . td <$> properties q
         predicate $ not (res `S.member` neededCols)

         return $ do
           logRewrite "Basic.ICols.Rownum" q
           replace q $(v "q1") |])

-- | Prune a rownumber operator if its output is not required
unreferencedRank :: TARule AllProps
unreferencedRank q =
  $(dagPatMatch 'q "[Rank | RowRank] args (q1)"
    [| do
         (res, _) <- return $(v "args")
         neededCols  <- pICols . td <$> properties q
         predicate $ not (res `S.member` neededCols)

         return $ do
           logRewrite "Basic.ICols.Rank" q
           replace q $(v "q1") |])

-- | Prune projections from a project operator if the result columns
-- are not required.
unreferencedProjectCols :: TARule AllProps
unreferencedProjectCols q =
  $(dagPatMatch 'q "Project projs (q1)"
    [| do
        neededCols <- pICols . td <$> properties q
        let neededProjs = filter (flip S.member neededCols . fst) $(v "projs")

        -- Only modify the project if we could actually get rid of some columns.
        predicate $ length neededProjs < length $(v "projs")

        return $ do
          logRewrite "Basic.ICols.Project" q
          void $ replaceWithNew q $ UnOp (Project neededProjs) $(v "q1") |])

-- | Remove aggregate functions whose output is not referenced.
unreferencedAggrCols :: TARule AllProps
unreferencedAggrCols q =
  $(dagPatMatch 'q "Aggr args (q1)"
    [| do
        neededCols <- pICols . td <$> properties q
        (aggrs, partCols) <- return $(v "args")

        let neededAggrs = filter (flip S.member neededCols . snd) aggrs

        predicate $ length neededAggrs < length aggrs

        return $ do
          case neededAggrs of
              -- If the output of all aggregate functions is not
              -- required, we can replace it with a distinct operator
              -- on the grouping columns.
              [] -> do
                  logRewrite "Basic.ICols.Aggr.PruneAggr" q
                  projectNode <- insert $ UnOp (Project partCols) $(v "q1")
                  void $ replaceWithNew q $ UnOp (Distinct ()) projectNode

              -- Otherwise, we just prune the unreferenced aggregate functions
              _ : _ -> do
                  logRewrite "Basic.ICols.Aggr.Narrow" q
                  void $ replaceWithNew q $ UnOp (Aggr (neededAggrs, partCols)) $(v "q1") |])

unreferencedLiteralCols :: TARule AllProps
unreferencedLiteralCols q =
  $(dagPatMatch 'q "LitTable tab "
    [| do
         neededCols <- pICols . td <$> properties q

         predicate (not $ S.null neededCols)

         let (tuples, schema)  = $(v "tab")

         predicate (not $ null tuples)

         predicate $ S.size neededCols < length schema

         return $ do

             let columns = transpose tuples
             let (reqCols, reqSchema) =
                  unzip
                  $ filter (\(_, (colName, _)) -> colName `S.member` neededCols)
                  $ zip columns schema
             let reqTuples = transpose reqCols

             void $ replaceWithNew q $ NullaryOp $ LitTable (reqTuples, reqSchema) |])

--------------------------------------------------------------------------------
-- Rewrites based on functional dependencies

-- | Helper function for 'prunePartExprs': Consider one particular not
-- required column and check wether it is functionally determined by
-- required columns and some other not required columns.
prunePartCols :: [(PartAttr, Attr)]  -- ^ Columns to consider for removal
              -> FDSet
              -> [(PartAttr, Attr)]  -- ^ Columns that will be preserved
              -> S.Set Attr          -- ^ Required columns
              -> S.Set (S.Set Attr)  -- ^ All determinant sets to consider
              -> [(PartAttr, Attr)]
prunePartCols []             _   reqProj _       _    = reqProj
prunePartCols ((c, gc) : ts) fds reqProj reqCols dets =
    case find (coveredCol fds gc) dets' of
        -- 'det' determines 'gc' -> remove 'gc'
        Just det ->
            let -- Columns that are not required downstream but that
                -- are part of the determinant set that determines gc
                -- and need to be preserved.
                unreqDetCols = S.intersection det otherUnreqCols

                -- remove all unrequired columns that are in the
                -- determinant set from the set of columns to consider
                -- for removal
                (keepProjs, ts')  = partition (\dc -> snd dc `S.member` unreqDetCols)
                                              ts

                -- if '(c, gc)' can be removed, all other (not
                -- required) projections '(c', gc)' can be removed as
                -- well.
                ts'' = filter ((/= gc) . snd) ts'

                -- Preserve all columns that are part of the
                -- determinant set just used.
                nextReqProjs = keepProjs ++ reqProj

                -- The set of columns that we keep in any case,
                -- including the columns in 'det'.
                nextReqCols = (unreqDetCols ∪ reqCols)

                -- Remove all determinant sets that contain the column
                -- we just removed.
                nextDets = S.filter (\ds -> not $ gc `S.member` ds) dets

            in prunePartCols ts'' fds nextReqProjs nextReqCols nextDets


        -- 'gc' is not determined by any remaining determinant set.
        Nothing  ->
            let nextReqProjs = (c, gc) : reqProj
                nextReqCols  = S.insert gc reqCols
                -- If gc is required, we can still remove all other
                -- occurences of gc: For grouping semantics, one
                -- occurence is enough. Furthermore, we know that all
                -- grouping projections in 'ts' are /not/ required
                -- from above (icols).
                ts'          = filter ((/= gc) . snd) ts
            in prunePartCols ts' fds nextReqProjs nextReqCols dets

  where
    otherUnreqCols = S.fromList $ map snd ts
    candCols = reqCols ∪ otherUnreqCols
    dets' = S.filter (`S.isSubsetOf` candCols) dets

-- | Prune not required grouping columns that are functionally
-- determined by a set of other grouping columns.
--
-- The key to efficiently check wether a column is determined by a set
-- of columns is not to consider some subsets of the columns that
-- /might/ form a determinant set. Instead, we check exactly those
-- subsets that occur as determinant sets in the set of functional
-- dependencies.
--
-- This is a heuristic optimization and does not result in the exact
-- optimum: Computing the minimum set of non-required columns such
-- that the grouping is equivalent to the original grouping seems to
-- be considerably harder.
prunePartExprs :: S.Set Attr               -- ^ Columns required from above
               -> [(PartAttr, Expr)]       -- ^ Grouping projections
               -> FDSet                    -- ^ All available FDs
               -> [(PartAttr, Expr)]
prunePartExprs icols groupProjs fds =
    -- trace ("PRUNEPARTEXPRS REQPARTCOLS " ++ show reqPartCols) $
    -- trace ("PRUNEPARTEXPRS NOTREQPARTCOLS " ++ show notReqPartCols) $
    -- trace ("PRUNEPARTEXPRS DETS " ++ showSet (showSet id) dets) $
    partExprs
    ++ map mkExp reqPartCols
    ++ map mkExp (prunePartCols notReqPartCols' fds [] reqCols dets)
  where
    dets = S.filter (`S.isSubsetOf` allCols)
           $ S.fromList $ M.keys $ fdsRep fds

    f :: (PartAttr, Expr) -> Either (PartAttr, Expr) (PartAttr, Attr)
    f (c, ColE gc) = Right (c, gc)
    f (c, e)       = Left (c, e)

    mkExp :: (PartAttr, Attr) -> (PartAttr, Expr)
    mkExp (c, gc) = (c, ColE gc)

    (partExprs, partCols) = partitionEithers $ map f groupProjs

    (reqPartCols, notReqPartCols) = partition (\gp -> fst gp `S.member` icols)
                                              partCols

    -- Seed the set of required grouping columns with those who are
    -- required from above.
    reqCols = S.fromList $ map snd reqPartCols

    -- Before considering non-trivial functional dependencies, we try
    -- to remove grouping columns based on trivial functional
    -- dependencies: If the projection column of a grouping projection
    -- is not required from above and the corresponding grouping
    -- column is already present in the set of required grouping
    -- columns, the projection can be safely removed.
    notReqPartCols' = filter (\(_, gc) -> not $ gc `S.member` reqCols)
                             notReqPartCols

    allCols = S.fromList $ map snd partCols

-- | Determine wether a column c is functionally determined by a
-- set of columns.
coveredCol :: FDSet -> Attr -> S.Set Attr -> Bool
coveredCol fds c cs =
    case M.lookup cs (fdsRep fds) of
        Just deps -> c `S.member` deps
        Nothing   -> False

triviallyCovered :: S.Set Attr -> Attr -> Bool
triviallyCovered cs c = c `S.member` cs

-- | Prune unreferenced grouping columns based on functional
-- dependencies.
unreferencedGroupingCols :: TARule AllProps
unreferencedGroupingCols q =
  $(dagPatMatch 'q "Aggr args (q1)"
    [| do
        neededCols        <- pICols . td <$> properties q
        fds               <- pFunDeps . bu <$> properties $(v "q1")
        (aggrs, partCols) <- return $(v "args")

        predicate $ not $ S.null $ S.fromList (map fst partCols) S.\\ neededCols
        predicate $ length partCols > 1

        let partCols' = prunePartExprs neededCols partCols fds

        predicate $ length partCols' < length partCols

        return $ do
          logRewrite "Basic.ICols.Aggr.PruneGroupingCols" q
          void $ replaceWithNew q $ UnOp (Aggr (aggrs, partCols')) $(v "q1") |])

--------------------------------------------------------------------------------

-- | Prune ordering columns that are functionally determined by
-- preceding columns.
pruneOrdColsFD :: FDSet -> [OrdCol] -> [OrdCol]
pruneOrdColsFD fds = go S.empty
  where
    go :: S.Set Attr -> [OrdCol] -> [OrdCol]
    go cs (OrdCol c (ColE oc) : ocs)
        | any (coveredCol fds oc) dets
            = go cs ocs
        | otherwise
            = OrdCol c (ColE oc) : go (S.insert oc cs) ocs
       where
         dets  = S.filter (`S.isSubsetOf` cs)
                 $ S.fromList $ M.keys $ fdsRep fds
    go cs (OrdCol c e : ocs) = OrdCol c e : go cs ocs
    go _  []                       = []

isAscOrd :: OrdCol -> Bool
isAscOrd (OrdCol (_, Asc) _) = True
isAscOrd _                   = False

-- | Prune ordering columns based on functional dependenices.
pruneSerializeSortColsFD :: TARule AllProps
pruneSerializeSortColsFD q =
  $(dagPatMatch 'q "Serialize args (q1)"
    [| do
        fds                  <- pFunDeps . bu <$> properties $(v "q1")
        (rcs, kcs, ocs, pcs) <- return $(v "args")
        -- trace ("SERIALIZE OCS " ++ show ocs) $ return ()
        -- trace ("SERIALIZE FDS " ++ show fds) $ return ()

        -- We restrict pruning to all-ascending orders for a simple
        -- reason: We have no clue what should happen if there are
        -- descending orders as well.
        predicate $ all isAscOrd ocs

        let ocs' = pruneOrdColsFD fds ocs
        predicate $ length ocs' < length ocs

        return $ do
          logRewrite "Basic.ICols.Serialize.PruneSortingCols.FD" q
          let args' = (rcs, kcs, ocs', pcs)
          void $ replaceWithNew q $ UnOp (Serialize args') $(v "q1") |])

--------------------------------------------------------------------------------

-- | Prune ordering expressions that occur more than once
pruneOrdCols :: [OrdCol] -> [OrdCol]
pruneOrdCols = go S.empty
  where
    go :: S.Set Expr -> [OrdCol] -> [OrdCol]
    go es (OrdCol c e : ocs)
        | S.member e es
            = go es ocs
        | otherwise
            = OrdCol c e : go (S.insert e es) ocs
    go _  [] = []

-- | Eliminate ordering expressions that occur more than once.
pruneSerializeSortCols :: TARule ()
pruneSerializeSortCols q =
  $(dagPatMatch 'q "Serialize args (q1)"
    [| do
        (rcs, kcs, ocs, pcs) <- return $(v "args")
        -- trace ("SERIALIZE OCS " ++ show ocs) $ return ()
        -- trace ("SERIALIZE FDS " ++ show fds) $ return ()

        -- We restrict pruning to all-ascending orders for a simple
        -- reason: We have no clue what should happen if there are
        -- descending orders as well.
        predicate $ all isAscOrd ocs

        let ocs' = pruneOrdCols ocs
        predicate $ length ocs' < length ocs

        return $ do
          logRewrite "Basic.Serialize.PruneSortingCols" q
          let args' = (rcs, kcs, ocs', pcs)
          void $ replaceWithNew q $ UnOp (Serialize args') $(v "q1") |])

----------------------------------------------------------------------------------
-- Basic Const rewrites

isConstExpr :: [ConstCol] -> Expr -> Bool
isConstExpr constCols e = isJust $ constExpr constCols e

constTrueJoinConjunct :: [ConstCol] -> [ConstCol] -> (Expr, Expr, JoinRel) -> Bool
constTrueJoinConjunct constColsLeft constColsRight (leftExpr, rightExpr, op) =
    fromMaybe False $ isConstantTrue op
                          <$> constExpr constColsLeft leftExpr
                          <*> constExpr constColsRight rightExpr

  where
    isConstantTrue EqJ v1 v2 = v1 == v2
    isConstantTrue GtJ v1 v2 = v1 >  v2
    isConstantTrue GeJ v1 v2 = v1 >= v2
    isConstantTrue LtJ v1 v2 = v1 <  v2
    isConstantTrue LeJ v1 v2 = v1 <= v2
    isConstantTrue NeJ v1 v2 = v1 /= v2

-- | Eliminate conjuncts from join predicates that are constant true.
constJoinPred :: TARule AllProps
constJoinPred q =
  $(dagPatMatch 'q "(q1) [ThetaJoin | AntiJoin | SemiJoin]@joinOp p (q2)"
    [| do
        constColsLeft  <- pConst . bu <$> properties $(v "q1")
        constColsRight <- pConst . bu <$> properties $(v "q2")
        let p' = filter (not . constTrueJoinConjunct constColsLeft constColsRight) $(v "p")
        predicate $ length p' < length $(v "p")
        -- FIXME if all conjuncts are constant, we can replace the join operator
        -- with either a cartesian product (thetajoin), the original left input
        -- (semijoin) or a constant false selection (antijoin).
        predicate $ not $ null p'

        return $ do
            logRewrite "Basic.Const.Join" q
            void $ replaceWithNew q $ BinOp ($(v "joinOp") p') $(v "q1") $(v "q2")
        |])

constMap :: [ConstCol] -> [Proj] -> [(Attr, AVal)]
constMap constCols =
    mapMaybe (\(c, e) -> (,) <$> pure c <*> constExpr constCols e)

-- | Prune const columns from aggregation keys
constAggrKey :: TARule AllProps
constAggrKey q =
  $(dagPatMatch 'q "Aggr args (q1)"
    [| do
         constCols   <- pConst . bu <$> properties $(v "q1")
         neededCols  <- S.toList . pICols . td <$> properties q
         (aggrFuns, keyCols@(_:_)) <- return $(v "args")

         let keyCols'   = filter (\(_, e) -> not $ isConstExpr constCols e) keyCols
             prunedKeys = map fst keyCols \\ map fst keyCols'

         predicate $ not $ null prunedKeys

         -- Some grouping column has to remain. Eliminating all grouping columns
         -- would effectively remove the GROUP BY clause and change the
         -- semantics of the SQL query (NULL values instead of an empty result).
         predicate $ not $ null keyCols'

         return $ do
             logRewrite "Basic.Const.Aggr" q
             let necessaryKeys = prunedKeys `intersect` neededCols

                 constProj c   = (\val -> (c, ConstE val)) <$> lookup c (constMap constCols keyCols)

                 constProjs    = mapMaybe constProj necessaryKeys

                 proj          = map (\(_, c) -> (c, ColE c)) aggrFuns
                                 ++
                                 map (\(c, _) -> (c, ColE c)) keyCols'
                                 ++
                                 constProjs


             aggrNode <- insert $ UnOp (Aggr ($(v "aggrFuns"), keyCols')) $(v "q1")
             void $ replaceWithNew q $ UnOp (Project proj) aggrNode |])

constRownumCol :: TARule AllProps
constRownumCol q =
  $(dagPatMatch 'q "RowNum args (q1)"
    [| do
         constCols <- pConst . bu <$> properties $(v "q1")

         (resCol, sortCols, partExprs) <- return $(v "args")
         let sortCols' = filter (\(e, _) -> not $ isConstExpr constCols e) sortCols
         predicate $ length sortCols' < length sortCols

         return $ do
             logRewrite "Basic.Const.RowNum" q
             void $ replaceWithNew q $ UnOp (RowNum (resCol, sortCols', partExprs)) $(v "q1") |])

constRowRankCol :: TARule AllProps
constRowRankCol q =
  $(dagPatMatch 'q "RowRank args (q1)"
    [| do
         constCols          <- pConst . bu <$> properties $(v "q1")
         (resCol, sortCols) <- return $(v "args")
         let sortCols' = filter (\(e, _) -> not $ isConstExpr constCols e) sortCols
         predicate $ length sortCols' < length sortCols

         return $ do
             logRewrite "Basic.Const.RowRank" q
             void $ replaceWithNew q $ UnOp (RowRank (resCol, sortCols')) $(v "q1") |])

-- constSerializeCol :: TARule AllProps
-- constSerializeCol q =
--   $(dagPatMatch 'q "Serialize args (q1)"
--     [| do
--          (mDescr, RelPos sortCols, payload) <- return $(v "args")
--          constCols                          <- map fst <$> pConst <$> bu <$> properties $(v "q1")

--          let sortCols' = filter (\c -> c `notElem` constCols) sortCols
--          predicate $ length sortCols' < length sortCols

--          return $ do
--              logRewrite "Basic.Const.Serialize" q
--              void $ replaceWithNew q $ UnOp (Serialize (mDescr, RelPos sortCols', payload)) $(v "q1") |])

constWinOrderCol :: TARule AllProps
constWinOrderCol q =
  $(dagPatMatch 'q "WinFun args (q1)"
    [| do
         constCols <- pConst . bu <$> properties $(v "q1")
         let (f, part, sortCols, frameSpec) = $(v "args")
         let sortCols' = filter (\(e, _) -> not $ isConstExpr constCols e) sortCols
         predicate $ length sortCols' < length sortCols

         return $ do
             logRewrite "Basic.Const.WinFun" q
             void $ replaceWithNew q $ UnOp (WinFun (f, part, sortCols', frameSpec)) $(v "q1") |])

singletonProductRight :: TARule AllProps
singletonProductRight q =
  $(dagPatMatch 'q "(q1) Cross _ (q2)"
    [| do
         cols1 <- pCols . bu <$> properties $(v "q1")
         props <- bu <$> properties $(v "q2")
         let constCols = pConst props
             card1     = pCard1 props
             cols2     = pCols props

         predicate card1
         Just constVals <- return $ traverse (\(c, _) -> (\val -> (c, val)) <$> lookup c constCols) $ S.toList cols2
         return $ do
             logRewrite "Basic.Const.Cross.Right" q
             let proj = [ (c, ColE c) | (c, _) <- S.toList cols1 ]
                        ++
                        [ (c, ConstE val) | (c, val) <- constVals ]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "q1") |])

singletonProductLeft :: TARule AllProps
singletonProductLeft q =
  $(dagPatMatch 'q "(q1) Cross _ (q2)"
    [| do
         cols2 <- pCols . bu <$> properties $(v "q2")
         props <- bu <$> properties $(v "q1")
         let constCols = pConst props
             card1     = pCard1 props
             cols1     = pCols props

         predicate card1
         Just constVals <- return $ traverse (\(c, _) -> (\val -> (c, val)) <$> lookup c constCols) $ S.toList cols1
         return $ do
             logRewrite "Basic.Const.Cross.Left" q
             let proj = [ (c, ConstE val) | (c, val) <- constVals ]
                        ++
                        [ (c, ColE c) | (c, _) <- S.toList cols2 ]
             void $ replaceWithNew q $ UnOp (Project proj) $(v "q2") |])

----------------------------------------------------------------------------------
-- Basic Order rewrites

-- | @lookupSortCol@ returns @Left@ if there is no mapping from the
-- original sort column and @Right@ if there is a mapping from the
-- original sort column to a list of columns that define the same
-- order.
lookupSortCol :: SortSpec -> Orders -> Either [SortSpec] [SortSpec]
lookupSortCol (ColE oldSortCol, Asc) os =
    case lookup oldSortCol os of
        Nothing          -> Left [(ColE oldSortCol, Asc)]
        Just newSortCols -> Right $ map (\c -> (ColE c, Asc)) newSortCols
-- We do not inline into arbitrary expressions for now. Likewise, we
-- do not consider non-ascending sorting.
lookupSortCol (e, dir)               _  = Left [(e, dir)]

inlineSortColsRownum :: TARule AllProps
inlineSortColsRownum q =
  $(dagPatMatch 'q "RowNum o (q1)"
    [| do
        (resCol, sortCols@(_:_), groupCols) <- return $(v "o")

        predicate $ all ((== Asc) . snd) sortCols

        orders@(_:_) <- pOrder . bu <$> properties $(v "q1")

        -- For each sorting column, try to find the original
        -- order-defining sorting columns.
        let mSortCols = map (`lookupSortCol` orders) sortCols

        -- The rewrite should only fire if something actually changes
        predicate $ any isRight mSortCols

        let sortCols' = nub $ concatMap (either id id) mSortCols

        return $ do
          logRewrite "Basic.InlineOrder.RowNum" q
          void $ replaceWithNew q $ UnOp (RowNum (resCol, sortCols', groupCols)) $(v "q1") |])

-- inlineSortColsSerialize :: TARule AllProps
-- inlineSortColsSerialize q =
--   $(dagPatMatch 'q "Serialize scols (q1)"
--     [| do
--         (d, RelPos cs, reqCols) <- return $(v "scols")
--         orders@(_:_) <- pOrder <$> bu <$> properties $(v "q1")

--         let cs' = nub $ concatMap (\c -> maybe [c] id $ lookup c orders) cs
--         predicate $ cs /= cs'

--         return $ do
--             logRewrite "Basic.InlineOrder.Serialize" q
--             void $ replaceWithNew q $ UnOp (Serialize (d, RelPos cs', reqCols)) $(v "q1") |])

inlineSortColsWinFun :: TARule AllProps
inlineSortColsWinFun q =
  $(dagPatMatch 'q "WinFun args (q1)"
    [| do
        let (f, part, sortCols, frameSpec) = $(v "args")

        orders@(_:_) <- pOrder . bu <$> properties $(v "q1")

        -- For each sorting column, try to find the original
        -- order-defining sorting columns.
        let mSortCols = map (`lookupSortCol` orders) sortCols

        -- The rewrite should only fire if something actually changes
        predicate $ any isRight mSortCols

        let sortCols' = nub $ concatMap (either id id) mSortCols
            args'     = (f, part, sortCols', frameSpec)

        return $ do
            logRewrite "Basic.InlineOrder.WinFun" q
            void $ replaceWithNew q $ UnOp (WinFun args') $(v "q1") |])

isKeyPrefix :: S.Set PKey -> [SortSpec] -> Bool
isKeyPrefix keys orderCols =
    case mapM (mColE . fst) orderCols of
        Just cols -> S.fromList cols `S.member` keys
        Nothing   -> False

-- | If a prefix of the ordering columns in a rownum operator forms a
-- key, the suffix can be removed.
keyPrefixOrdering :: TARule AllProps
keyPrefixOrdering q =
  $(dagPatMatch 'q "RowNum args (q1)"
    [| do
        (resCol, sortCols, []) <- return $(v "args")
        keys                   <- pKeys . bu <$> properties $(v "q1")

        predicate $ not $ null sortCols

        -- All non-empty and incomplete prefixes of the ordering
        -- columns
        let ordPrefixes = init $ drop 1 (inits sortCols)
        Just prefix <- return $ find (isKeyPrefix keys) ordPrefixes

        return $ do
            logRewrite "Basic.SimplifyOrder.KeyPrefix" q
            let sortCols' = take (length prefix) sortCols
            void $ replaceWithNew q $ UnOp (RowNum (resCol, sortCols', [])) $(v "q1") |])

duplicateSortingCriteriaRownum :: TARule ()
duplicateSortingCriteriaRownum q =
  $(dagPatMatch 'q "RowNum args (q1)"
    [| do
        (resCol, sortCols, []) <- return $(v "args")

        let sortCols' = nub sortCols

        predicate $ length sortCols' < length sortCols

        return $ do
            logRewrite "Basic.SimplifyOrder.Duplicates.Rownum" q
            let args' = (resCol, sortCols', [])
            void $ replaceWithNew q $ UnOp (RowNum args') $(v "q1") |])

duplicateSortingCriteriaWin :: TARule ()
duplicateSortingCriteriaWin q =
  $(dagPatMatch 'q "WinFun args (q1)"
    [| do
        let (winFuns, part, sortCols, mFrameBounds) = $(v "args")

        let sortCols' = nub sortCols

        predicate $ length sortCols' < length sortCols

        return $ do
            logRewrite "Basic.SimplifyOrder.Duplicates.WinFun" q
            let args' = (winFuns, part, sortCols', mFrameBounds)
            void $ replaceWithNew q $ UnOp (WinFun args') $(v "q1") |])

-- duplicateSortingCriteriaSerialize :: TARule ()
-- duplicateSortingCriteriaSerialize q =
--   $(dagPatMatch 'q "Serialize args (q1)"
--     [| do
--         (mDescr, RelPos sortCols, payload) <- return $(v "args")
--         let sortCols' = nub sortCols

--         predicate $ length sortCols' < length sortCols

--         return $ do
--             logRewrite "Basic.SimplifyOrder.Duplicates.Serialize" q
--             let args' = (mDescr, RelPos sortCols', payload)
--             void $ replaceWithNew q $ UnOp (Serialize args') $(v "q1") |])

-- | If a rownum output is not refererenced by a parent projection,
-- discard it. This handles the case of a multi-parent rownum that is
-- not required by a specific parent but is required by other parents
-- and therefore can't be eliminated globally.
--
-- FIXME It would be more elegant and general to make the ICols
-- analysis parent-aware so that we can tell for an operator wether it
-- is required by a specific parent.
bypassRownumProject :: TARule ()
bypassRownumProject q =
  $(dagPatMatch 'q "Project p (RowNum s (q1))"
    [| do
          let (resCol, _, _) = $(v "s")
          predicate $ not $ S.member resCol (S.unions $ map (exprCols . snd) $(v "p"))
          return $ do
              logRewrite "Basic.SimplifyOrder.BypassRownum" q
              void $ replaceWithNew q $ UnOp (Project $(v "p")) $(v "q1") |])

----------------------------------------------------------------------------------
-- Serialize rewrites

-- -- | Merge a projection which only maps columns into a Serialize operator.
-- serializeProject :: TARule ()
-- serializeProject q =
--     $(dagPatMatch 'q "Serialize scols (Project projs (q1))"
--       [| do
--           (d, p, reqCols) <- return $(v "scols")

--           let projCol (c', ColE c) = return (c', c)
--               projCol _            = fail "no match"

--               lookupFail x xys = case lookup x xys of
--                   Just y  -> return y
--                   Nothing -> fail "no match"

--           colMap <- mapM projCol $(v "projs")

--           -- find new names for all required columns
--           reqCols' <- mapM (\(PayloadCol c) -> PayloadCol <$> lookupFail c colMap) reqCols

--           -- find new name for the descriptor column (if required)
--           d' <- case d of
--               Just (DescrCol c)  -> Just <$> DescrCol <$> lookupFail c colMap
--               Nothing            -> return Nothing

--           -- find new name for the pos column (if required)
--           p' <- case p of
--               AbsPos c  -> AbsPos <$> lookupFail c colMap
--               RelPos cs -> RelPos <$> mapM (flip lookupFail colMap) cs
--               NoPos     -> return NoPos

--           return $ do
--               logRewrite "Basic.Serialize.Project" q
--               void $ replaceWithNew q $ UnOp (Serialize (d', p', reqCols')) $(v "q1") |])

--------------------------------------------------------------------------------
-- Pulling projections through other operators and merging them into
-- other operators

inlineExpr :: [Proj] -> Expr -> Expr
inlineExpr proj expr =
    case expr of
        BinAppE op e1 e2 -> BinAppE op (inlineExpr proj e1) (inlineExpr proj e2)
        UnAppE op e      -> UnAppE op (inlineExpr proj e)
        ColE c           -> fromMaybe (failedLookup c) (lookup c proj)
        ConstE val       -> ConstE val
        IfE c t e        -> IfE (inlineExpr proj c) (inlineExpr proj t) (inlineExpr proj e)

  where
    failedLookup :: Attr -> a
    failedLookup c = trace (printf "mergeProjections: column lookup %s failed\n%s\n%s"
                                   c (show expr) (show proj))
                           $impossible

mergeProjections :: [Proj] -> [Proj] -> [Proj]
mergeProjections proj1 proj2 = map (second (inlineExpr proj2)) proj1

stackedProject :: TARule ()
stackedProject q =
  $(dagPatMatch 'q "Project ps1 (Project ps2 (qi))"
    [| do
         return $ do
           let ps = mergeProjections $(v "ps1") $(v "ps2")
           logRewrite "Basic.Project.Merge" q
           void $ replaceWithNew q $ UnOp (Project ps) $(v "qi") |])



mapWinFun :: (Expr -> Expr) -> WinFun -> WinFun
mapWinFun f (WinMax e)        = WinMax $ f e
mapWinFun f (WinMin e)        = WinMin $ f e
mapWinFun f (WinSum e)        = WinSum $ f e
mapWinFun f (WinAvg e)        = WinAvg $ f e
mapWinFun f (WinAll e)        = WinAll $ f e
mapWinFun f (WinAny e)        = WinAny $ f e
mapWinFun f (WinFirstValue e) = WinFirstValue $ f e
mapWinFun f (WinLastValue e)  = WinLastValue $ f e
mapWinFun _ WinCount          = WinCount

mapAggrFun :: (Expr -> Expr) -> AggrType -> AggrType
mapAggrFun f (Max e)   = Max $ f e
mapAggrFun f (Min e)   = Min $ f e
mapAggrFun f (Sum e)   = Sum $ f e
mapAggrFun f (Avg e)   = Avg $ f e
mapAggrFun f (All e)   = All $ f e
mapAggrFun f (Any e)   = Any $ f e
mapAggrFun f (Count e) = Count $ f e
mapAggrFun _ CountStar = CountStar

nameChangeProj :: (Attr, Expr) -> Either (Attr, Attr) (Attr, Expr)
nameChangeProj (c, ColE c') | c /= c' = Left (c, c')
nameChangeProj (c, e)                 = Right (c, e)

-- | If grouping columns are renamed, move renaming to a
-- projection. This makes plans more readable by keeping base table
-- names and should lead to more compact SQL code (less column
-- renaming)
pullProjectAggr :: TARule ()
pullProjectAggr q =
    $(dagPatMatch 'q "Aggr args (q1)"
      [| do
          let (as, gs) = $(v "args")
          -- Check wether there are projections that only change an
          -- attribute name
          let (gnps, gps) = partitionEithers $ map nameChangeProj gs
          predicate $ not $ null gnps

          -- Check that the original name in a grouping projection
          -- does not collide with one of the output names for
          -- aggregates.
          predicate $ null $ map snd gnps `intersect` map snd as

          return $ do
              logRewrite "Basic.PullProject.Aggr" q

              let gs'  = nub $ gps ++ map (\(_, c) -> (c, ColE c)) gnps
                  proj = map (\(_, c) -> (c, ColE c)) as
                         ++ map (\(c, _) -> (c, ColE c)) gps
                         ++ map (second ColE) gnps

              aggrNode <- insert $ UnOp (Aggr (as, gs')) $(v "q1")
              void $ replaceWithNew q $ UnOp (Project proj) aggrNode |])


pullProjectWinFun :: TARule ()
pullProjectWinFun q =
    $(dagPatMatch 'q "WinFun args (Project proj (q1))"
      [| do
          -- Only consider window functions without partitioning for
          -- now. Partitioning requires proper values and inlining
          -- would be problematic.
          ((resCol, f), [], sortSpec, frameSpec) <- return $(v "args")

          -- If the window function result overwrites one of the
          -- projection columns, we can't pull.
          predicate $ resCol `notElem` map fst $(v "proj")

          return $ do
              logRewrite "Basic.PullProject.WinFun" q

              -- Merge the projection expressions into window function
              -- arguments and ordering expressions.
              let f'        = mapWinFun (inlineExpr $(v "proj")) f

                  sortSpec' = map (first (inlineExpr $(v "proj"))) sortSpec

                  proj'     = $(v "proj") ++ [(resCol, ColE resCol)]

              winNode <- insert $ UnOp (WinFun ((resCol, f'), [], sortSpec', frameSpec)) $(v "q1")
              void $ replaceWithNew q $ UnOp (Project proj') winNode |])

pullProjectSerialize :: TARule ()
pullProjectSerialize q =
    $(dagPatMatch 'q "Serialize args (Project proj (q1))"
      [| do
          return $ do
              logRewrite "Basic.PullProject.Serialize" q
              let (rcs, kcs, ocs, pcs) = $(v "args")
              let rcs' = [ RefCol c (inlineExpr $(v "proj") e) | RefCol c e <- rcs ]
                  kcs' = [ KeyCol c (inlineExpr $(v "proj") e) | KeyCol c e <- kcs ]
                  ocs' = [ OrdCol c (inlineExpr $(v "proj") e) | OrdCol c e <- ocs ]
                  pcs' = [ PayloadCol c (inlineExpr $(v "proj") e)
                         | PayloadCol c e <- pcs
                         ]

              void $ replaceWithNew q $ UnOp (Serialize (rcs', kcs', ocs', pcs')) $(v "q1") |])

pullProjectSelect :: TARule ()
pullProjectSelect q =
    $(dagPatMatch 'q "Select p (Project proj (q1))"
      [| do
          return $ do
              logRewrite "Basic.PullProject.Select" q
              let p' = inlineExpr $(v "proj") $(v "p")
              selectNode <- insert $ UnOp (Select p') $(v "q1")
              void $ replaceWithNew q $ UnOp (Project $(v "proj")) selectNode |])

mergeProjIntoSortSpec :: (Attr, [SortSpec], [PartExpr])
                      -> [(Attr, Expr)]
                      -> (Attr, [SortSpec], [PartExpr])
mergeProjIntoSortSpec (attr, sortSpec, partSpec) proj = (attr, sortSpec', partSpec')
  where
    sortSpec' = map (first (inlineExpr proj)) sortSpec
    partSpec' = map (inlineExpr proj) partSpec

pullProjectRownum :: TARule ()
pullProjectRownum q =
    $(dagPatMatch 'q "RowNum s (Project p (q1))"
      [| do
          let (resCol, _, _) = $(v "s")

          -- If the rownum overwrites one of the columns generated by
          -- the projection, remove it from the projection.
          let p' = [ (a, e) | (a, e) <- $(v "p"), a /= resCol ]

          -- Make sure that the rownum result column does not appear
          -- in one of the projection expressions to avoid shadowing.
          predicate $ not $ S.member resCol (S.unions $ map (exprCols . snd) p')

          return $ do
              logRewrite "Basic.PullProject.Rownum" q
              let p'' = p' ++ [(resCol, ColE resCol)]
                  s' = mergeProjIntoSortSpec $(v "s") $(v "p")
              rownumNode <- insert $ UnOp (RowNum s') $(v "q1")
              void $ replaceWithNew q $ UnOp (Project p'') rownumNode |])

inlineJoinPredRight :: [Proj] -> [(Expr, Expr, JoinRel)] -> [(Expr, Expr, JoinRel)]
inlineJoinPredRight proj = map inlineConjunct
  where
    inlineConjunct (le, re, rel) = (le, inlineExpr proj re, rel)

inlineJoinPredLeft :: [Proj] -> [(Expr, Expr, JoinRel)] -> [(Expr, Expr, JoinRel)]
inlineJoinPredLeft proj = map inlineConjunct
  where
    inlineConjunct (le, re, rel) = (inlineExpr proj le, re, rel)

pullProjectSemiJoinLeft :: TARule ()
pullProjectSemiJoinLeft q =
    $(dagPatMatch 'q "(Project proj (q1)) [SemiJoin | AntiJoin]@joinOp p (q2)"
      [| do
          return $ do
              logRewrite "Basic.PullProject.SemiJoin.Left" q
              let p' = inlineJoinPredLeft $(v "proj") $(v "p")
              joinNode <- insert $ BinOp ($(v "joinOp") p') $(v "q1") $(v "q2")
              void $ replaceWithNew q $ UnOp (Project $(v "proj")) joinNode |])

pullProjectSemiJoinRight :: TARule ()
pullProjectSemiJoinRight q =
    $(dagPatMatch 'q "(q1) [SemiJoin | AntiJoin]@jop p (Project proj (q2))"
      [| do
          return $ do
              logRewrite "Basic.PullProject.SemiJoin.Right" q
              let p' = inlineJoinPredRight $(v "proj") $(v "p")
              void $ replaceWithNew q $ BinOp ($(v "jop") p') $(v "q1") $(v "q2") |])

pullProjectThetaJoinLeft :: TARule AllProps
pullProjectThetaJoinLeft q =
    $(dagPatMatch 'q "(Project p (q1)) [ThetaJoin | LeftOuterJoin]@op jp (q2)"
      [| do
          colsLeft  <- fmap fst <$> pCols <$> bu <$> properties $(v "q1")
          colsRight <- fmap fst <$> pCols <$> bu <$> properties $(v "q2")
          predicate $ S.null $ S.intersection colsLeft colsRight

          return $ do
              logRewrite "Basic.PullProject.Join.Left" q
              let jp' = inlineJoinPredLeft $(v "p") $(v "jp")
                  p'  = $(v "p")
                        ++
                        S.toList (fmap (\c -> (c, ColE c)) colsRight)
              joinNode <- insert $ BinOp ($(v "op") jp') $(v "q1") $(v "q2")
              void $ replaceWithNew q $ UnOp (Project p') joinNode |])

pullProjectThetaJoinRight :: TARule AllProps
pullProjectThetaJoinRight q =
    $(dagPatMatch 'q "(q1) [ThetaJoin | LeftOuterJoin]@op jp (Project p (q2))"
      [| do
          colsLeft  <- fmap fst <$> pCols <$> bu <$> properties $(v "q1")
          colsRight <- fmap fst <$> pCols <$> bu <$> properties $(v "q2")
          predicate $ S.null $ S.intersection colsLeft colsRight

          return $ do
              logRewrite "Basic.PullProject.Join.Right" q
              let jp' = inlineJoinPredRight $(v "p") $(v "jp")
                  p'  = S.toList (fmap (\c -> (c, ColE c)) colsLeft)
                        ++
                        $(v "p")
              joinNode <- insert $ BinOp ($(v "op") jp') $(v "q1") $(v "q2")
              void $ replaceWithNew q $ UnOp (Project p') joinNode |])

pullProjectCrossLeft :: TARule AllProps
pullProjectCrossLeft q =
    $(dagPatMatch 'q "(Project p (q1)) Cross _ (q2)"
      [| do
          colsLeft  <- fmap fst <$> pCols <$> bu <$> properties $(v "q1")
          colsRight <- fmap fst <$> pCols <$> bu <$> properties $(v "q2")
          predicate $ S.null $ S.intersection colsLeft colsRight

          return $ do
              logRewrite "Basic.PullProject.Cross.Left" q
              let p'  = $(v "p")
                        ++
                        S.toList (fmap (\c -> (c, ColE c)) colsRight)
              crossNode <- insert $ BinOp (Cross ()) $(v "q1") $(v "q2")
              void $ replaceWithNew q $ UnOp (Project p') crossNode |])

pullProjectCrossRight :: TARule AllProps
pullProjectCrossRight q =
    $(dagPatMatch 'q "(q1) Cross _ (Project p (q2))"
      [| do
          colsLeft  <- fmap fst <$> pCols <$> bu <$> properties $(v "q1")
          colsRight <- fmap fst <$> pCols <$> bu <$> properties $(v "q2")
          predicate $ S.null $ S.intersection colsLeft colsRight

          return $ do
              logRewrite "Basic.PullProject.Cross.Right" q
              let p'  = S.toList (fmap (\c -> (c, ColE c)) colsLeft)
                        ++
                        $(v "p")
              crossNode <- insert $ BinOp (Cross ()) $(v "q1") $(v "q2")
              void $ replaceWithNew q $ UnOp (Project p') crossNode |])

inlineProjectAggr :: TARule ()
inlineProjectAggr q =
    $(dagPatMatch 'q "Aggr args (Project p (q1))"
      [| do
          let (as, gs) = $(v "args")
          let inline = inlineExpr $(v "p")
          let as' = map (first (mapAggrFun inline)) as
              gs' = map (second inline) gs

          return $ do
              logRewrite "Basic.PullProject.Aggr" q
              void $ replaceWithNew q $ UnOp (Aggr (as', gs')) $(v "q1") |])

--------------------------------------------------------------------------------
-- Rewrites based on functional dependencies

