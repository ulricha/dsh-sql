module Database.DSH.Backend.Sql.Opt.OptimizeTA
    ( pgPipeline
    , m5Pipeline
    , hyperPipeline
    , defaultPipeline
    , optimizeTA
    ) where

import qualified Data.IntMap as M

import qualified Database.Algebra.Dag                              as Dag
import           Database.Algebra.Table.Lang

import           Database.DSH.Common.Opt

import           Database.DSH.Backend.Sql.Opt.Rewrite.Basic
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.Opt.Rewrite.Common
import           Database.DSH.Backend.Sql.Opt.Properties.Types
import           Database.DSH.Common.QueryPlan

type RewriteClass = Rewrite TableAlgebra (Shape TADVec) Bool

--------------------------------------------------------------------------------
-- Rewrite pipelines for various SQL dialects

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
               , inlineProjectAggr
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
                      , constFilteringJoinPred
                      , constJoinPred
                      , constAggrKey
                      , constRownumCol
                      , constRowRankCol
                      -- , constSerializeCol
                      , constWinOrderCol
                      , pullProjectThetaJoinLeft
                      , pullProjectThetaJoinRight
                      , pullProjectSemiJoinLeft
                      , pullProjectSemiJoinRight
                      , pullProjectCrossLeft
                      , pullProjectCrossRight
                      , singletonProductLeft
                      , singletonProductRight
                      ]

defaultPipeline :: [RewriteClass]
defaultPipeline = [cleanup]

--------------------------------------------------------------------------------

m5CleanupRules :: TARuleSet ()
m5CleanupRules = [ stackedProject
                 -- , serializeProject
                 , pullProjectWinFun
                 , pullProjectSelect
                 , pullProjectSerialize
                 -- Disable because MonetDB supports only column references in
                 -- the partitioning spec.
                 -- , pullProjectRownum
                 -- Disable because MonetDB supports only column references in
                 -- the grouping spec.
                 -- , pullProjectAggr
                 -- , inlineProjectAggr
                 , duplicateSortingCriteriaWin
                 , duplicateSortingCriteriaRownum
                 -- , duplicateSortingCriteriaSerialize
                 , bypassRownumProject
                 , pruneSerializeSortCols
                 ]

m5Cleanup :: TARewrite Bool
m5Cleanup = iteratively $ sequenceRewrites [ applyToAll noProps m5CleanupRules
                                           , applyToAll inferAll cleanupRulesTopDown
                                           ]

--------------------------------------------------------------------------------
-- Rewrite pipelines for all supported SQL dialects

pgPipeline :: [RewriteClass]
pgPipeline = defaultPipeline

m5Pipeline :: [RewriteClass]
m5Pipeline = [m5Cleanup]

hyperPipeline :: [RewriteClass]
hyperPipeline = defaultPipeline

--------------------------------------------------------------------------------

-- | Apply a rewrite pipeline to a relational plan
runPipeline :: Dag.AlgebraDag TableAlgebra
            -> Shape TADVec
            -> [RewriteClass]
            -> Bool
            -> (Dag.AlgebraDag TableAlgebra, Log, Shape TADVec)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

optimizeTA :: [RewriteClass] -> QueryPlan TableAlgebra TADVec -> QueryPlan TableAlgebra TADVec
optimizeTA pipeline plan =
#ifdef DEBUGGRAPH
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
#else
  let (d, _rewriteLog, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }
