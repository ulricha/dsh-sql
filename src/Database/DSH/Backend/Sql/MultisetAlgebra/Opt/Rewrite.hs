{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.MultisetAlgebra.Opt.Rewrite
    ( maRules
    ) where

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.VectorLang

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.Vector

--------------------------------------------------------------------------------
-- Types for MA rewrite rules

type MARule p = Rule MA p (Shape MADVec)
type MARuleSet p = RuleSet MA p (Shape MADVec)

--------------------------------------------------------------------------------
-- Rule sets

maRules :: MARuleSet ()
maRules = [ mergeProjection
          , pullProjectSelect
          , pullProjectRowNumPart
          , pullProjectGroupAggr
          , pullProjectThetaJoinLeft
          , pullProjectThetaJoinRight
          , pullProjectFilterJoinLeft
          , pullProjectFilterJoinRight
          , pullProjectCartProductLeft
          , pullProjectCartProductRight
          , pullProjectLeftOuterJoinLeft
          , pullProjectLeftOuterJoinRight
          , pullProjectGroupJoinLeft
          , pullProjectGroupJoinRight
          ]

--------------------------------------------------------------------------------
-- Rewrite rules: Projection pull-up

mergeProjection :: MARule ()
mergeProjection q =
    $(dagPatMatch 'q "Project e2 (Project e1 (q1))"
      [| do
            return $ do
                logRewrite "MA.Project.Merge" q
                let e2' = partialEval $ mergeExpr $(v "e1") $(v "e2")
                void $ replaceWithNew q $ UnOp (Project e2') $(v "q1")
       |])

pullProjectSelect :: MARule ()
pullProjectSelect q =
    $(dagPatMatch 'q "Select e2 (Project e1 (q1))"
      [| do
            return $ do
                logRewrite "MA.Project.Select" q
                let e2' = partialEval $ mergeExpr $(v "e1") $(v "e2")
                selectNode <- insert $ UnOp (Select e2') $(v "q1")
                void $ replaceWithNew q $ UnOp (Project e1) selectNode
       |])

pullProjectRowNumPart :: MARule ()
pullProjectRowNumPart q =
    $(dagPatMatch 'q "RowNumPart args (Project e (q1))"
      [| do
            return $ do
                logRewrite "MA.Project.RowNumPart" q
                let (part, ord) = $(v "args")
                    part'       = partialEval $ mergeExpr $(v "e") part
                    ord'        = partialEval $ mergeExpr $(v "e") ord
                    e'          = partialEval $ appExprFst $(v "e")
                numNode <- insert $ UnOp (RowNumPart (part', ord')) $(v "q1")
                void $ replaceWithNew q $ UnOp (Project e') numNode
       |])

pullProjectGroupAggr :: MARule ()
pullProjectGroupAggr q =
    $(dagPatMatch 'q "GroupAggr args (Project e (q1))"
      [| do
            return $ do
                logRewrite "MA.Project.GroupAggr" q
                let (g, as) = $(v "args")
                    g'      = partialEval $ mergeExpr $(v "e") g
                    as'     = fmap (partialEval . mergeExpr $(v "e") <$>) as
                void $ replaceWithNew q $ UnOp (GroupAggr (g', as')) $(v "q1")
       |])

pullProjectThetaJoinLeft :: MARule ()
pullProjectThetaJoinLeft q =
    $(dagPatMatch 'q "(Project e (q1)) ThetaJoin p (q2))"
      [| do
            return $ do
                logRewrite "MA.Project.ThetaJoin.Left" q
                let p' = partialEval <$> inlineJoinPredLeft $(v "e") p
                    e' = partialEval $ appExprFst $(v "e")
                joinNode <- insert $ BinOp (ThetaJoin p')  $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') joinNode
       |])

pullProjectThetaJoinRight :: MARule ()
pullProjectThetaJoinRight q =
    $(dagPatMatch 'q "(q1) ThetaJoin p (Project e (q2)))"
      [| do
            return $ do
                logRewrite "MA.Project.ThetaJoin.Right" q
                let p' = partialEval <$> inlineJoinPredRight $(v "e") p
                    e' = partialEval $ appExprSnd $(v "e")
                joinNode <- insert $ BinOp (ThetaJoin p')  $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') joinNode
       |])

pullProjectCartProductLeft :: MARule ()
pullProjectCartProductLeft q =
    $(dagPatMatch 'q "(Project e (q1)) CartProduct _ (q2))"
      [| do
            return $ do
                logRewrite "MA.Project.CartProduct.Left" q
                let e' = partialEval $ appExprFst $(v "e")
                prodNode <- insert $ BinOp (CartProduct ()) $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') prodNode
       |])

pullProjectCartProductRight :: MARule ()
pullProjectCartProductRight q =
    $(dagPatMatch 'q "(q1) CartProduct _ (Project e (q2)))"
      [| do
            return $ do
                logRewrite "MA.Project.CartProduct.Right" q
                let e' = partialEval $ appExprSnd $(v "e")
                prodNode <- insert $ BinOp (CartProduct ()) $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') prodNode
       |])

pullProjectFilterJoinLeft :: MARule ()
pullProjectFilterJoinLeft q =
    $(dagPatMatch 'q "(Project e (q1)) [SemiJoin | AntiJoin]@joinOp p (q2))"
      [| do
            return $ do
                logRewrite "MA.Project.FilterJoin.Left" q
                let p' = partialEval <$> inlineJoinPredLeft $(v "e") p
                joinNode <- insert $ BinOp ($(v "joinOp") p')  $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project $(v "e")) joinNode
       |])

pullProjectFilterJoinRight :: MARule ()
pullProjectFilterJoinRight q =
    $(dagPatMatch 'q "(q1) [SemiJoin | AntiJoin]@joinOp p (Project e (q2)))"
      [| do
            return $ do
                logRewrite "MA.Project.FilterJoin.Right" q
                let p' = partialEval <$> inlineJoinPredRight $(v "e") p
                void $ replaceWithNew q $ BinOp ($(v "joinOp") p')  $(v "q1") $(v "q2")
       |])

pullProjectLeftOuterJoinLeft :: MARule ()
pullProjectLeftOuterJoinLeft q =
    $(dagPatMatch 'q "(Project e (q1)) LeftOuterJoin args (q2))"
      [| do
            return $ do
                logRewrite "MA.Project.LeftOuterJoin.Left" q
                let (p, d, r) = $(v "args")
                    p'        = partialEval <$> inlineJoinPredLeft $(v "e") p
                    e'        = partialEval $ appExprFst $(v "e")
                joinNode <- insert $ BinOp (LeftOuterJoin (p', d, r))  $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') joinNode
       |])

pullProjectLeftOuterJoinRight :: MARule ()
pullProjectLeftOuterJoinRight q =
    $(dagPatMatch 'q "(q1) LeftOuterJoin args (Project e (q2)))"
      [| do
            return $ do
                logRewrite "MA.Project.RightOuterJoin.Right" q
                let (p, d, r) = $(v "args")
                    p'        = partialEval <$> inlineJoinPredRight $(v "e") p
                    r'        = partialEval $ mergeExpr $(v "e") r
                void $ replaceWithNew q $ BinOp (LeftOuterJoin (p', d, r'))  $(v "q1") $(v "q2")
       |])

pullProjectGroupJoinLeft :: MARule ()
pullProjectGroupJoinLeft q =
    $(dagPatMatch 'q "(Project e (q1)) GroupJoin args (q2))"
      [| do
            return $ do
                logRewrite "MA.Project.GroupJoin.Left" q
                let (p, as) = $(v "args")
                    p'      = partialEval <$> inlineJoinPredLeft $(v "e") p
                    as'     = fmap (fmap (partialEval . (mergeExpr $ appExprFst $(v "e")))) as
                    e'      = partialEval $ appExprFst $(v "e")
                joinNode <- insert $ BinOp (GroupJoin (p', as'))  $(v "q1") $(v "q2")
                void $ replaceWithNew q $ UnOp (Project e') joinNode
       |])

pullProjectGroupJoinRight :: MARule ()
pullProjectGroupJoinRight q =
    $(dagPatMatch 'q "(q1) GroupJoin args (Project e (q2)))"
      [| do
            return $ do
                logRewrite "MA.Project.GroupJoin.Right" q
                let (p, as) = $(v "args")
                    p'      = partialEval <$> inlineJoinPredRight $(v "e") p
                    as'     = fmap (fmap (partialEval . (mergeExpr $ appExprSnd $(v "e")))) as
                void $ replaceWithNew q $ BinOp (GroupJoin (p', as'))  $(v "q1") $(v "q2")
       |])
