{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Optimizer.VL.Rewrite.Window where

import Debug.Trace

import           Control.Applicative
import           Control.Monad
import           Data.List.NonEmpty                              (NonEmpty (..))

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang
import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Properties.ReqColumns
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.Optimizer.VL.Properties.VectorType
import           Database.DSH.Optimizer.VL.Rewrite.Common
import           Database.DSH.VL.Lang

pattern SingleJoinPred e1 op e2 = JoinPred ((JoinConjunct e1 op e2) :| [])
pattern DoubleJoinPred e11 op1 e12 e21 op2 e22 = JoinPred ((JoinConjunct e11 op1 e12)
                                                           :|
                                                           [JoinConjunct e21 op2 e22])
pattern AddExpr e1 e2 = BinApp (SBNumOp Add) e1 e2
pattern SubExpr e1 e2 = BinApp (SBNumOp Sub) e1 e2

aggrToWinFun :: AggrFun -> WinFun
aggrToWinFun (AggrSum _ e) = WinSum e
aggrToWinFun (AggrMin e)   = WinMin e
aggrToWinFun (AggrMax e)   = WinMax e
aggrToWinFun (AggrAvg e)   = WinAvg e
aggrToWinFun (AggrAll e)   = WinAll e
aggrToWinFun (AggrAny e)   = WinAny e
aggrToWinFun AggrCount     = WinCount

-- Turn a running aggregate based on a self-join into a window operator.
runningAggWin :: VLRule BottomUpProps
runningAggWin q =
  $(dagPatMatch 'q "(_) AggrS afun (R1 ((Segment (Number (q1))) ThetaJoin p (Number (q2))))"
    [| do
        predicate $ $(v "q1") == $(v "q2")

        w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        -- We require a range predicate on the positions generated by
        -- Number.
        -- FIXME allow other forms of window specifications
        SingleJoinPred (Column nrCol) GtE (Column nrCol') <- return $(v "p")
        predicate $ nrCol == w + 1 && nrCol' == w + 1

        -- The aggregate should only reference columns from the right
        -- ThetaJoin input, i.e. columns from the partition generated
        -- for a input tuple.
        let isWindowColumn c = c >= w + 2 && c <= 2 * w + 1
        predicate $ all isWindowColumn (aggrReqCols $(v "afun"))

        return $ do
            logRewrite "Window.RunningAggr" q
            -- Shift column references in aggregate functions so that
            -- they are applied to partition columns.
            let afun' = aggrToWinFun $ mapAggrFun (mapExprCols (\c -> c - (w + 1))) $(v "afun")

            -- The WinAggr operator /adds/ the window function output
            -- as a new column but keeps the old columns. Because we
            -- introduce WinAggr starting with Aggrs which only
            -- produces the aggregate output, we have to insert a
            -- projection to remove the original input columns and
            -- only keep the window function output.
            winNode <- insert $ UnOp (WinFun (afun', FAllPreceding)) $(v "q1")
            void $ replaceWithNew q $ UnOp (Project [Column $ w + 1]) winNode |])

firstValueWin :: VLRule Properties
firstValueWin q =
  $(dagPatMatch 'q "(UnboxRename (Number (q1))) PropRename (R1 (SelectPos1S selectArgs (R1 ((Segment (Number (q2))) ThetaJoin joinPred (Number (q3))))))"
    [| do
        predicate $ $(v "q1") == $(v "q2") && $(v "q1") == $(v "q3")

        w <- vectorWidth <$> vectorTypeProp <$> bu <$> properties $(v "q1")

        VProp (Just [3]) <- reqColumnsProp <$> td <$> properties $(v "q")

        -- The evaluation of first_value produces only a single value
        -- for each input column. To employ first_value, the input has
        -- to consist of a single column.

        -- FIXME this is propably too fragile. We could alternatively
        -- demand that only one column is required from the
        -- UnboxRename output.
        predicate $ w == 1

        -- We expect the VL representation of 'head'
        (SBRelOp Eq, N 1) <- return $(v "selectArgs")
  
        -- We expect a window specification that for each element
        -- includes its predecessor (if there is one) and the element
        -- itself.
        DoubleJoinPred e11 op1 e12 e21 op2 e22                   <- return $(v "joinPred")
        (SubExpr (Column nrCol) frameOffset, LtE, Column nrCol') <- return (e11, op1, e12)
        (Column nrCol'', GtE, Column nrCol''')                   <- return (e21, op2, e22)
        Constant (VLInt offset)                                  <- return frameOffset

        -- Check that all (assumed) numbering columns are actually the
        -- column added by the Number operator.
        predicate $ all (== 2) [nrCol, nrCol', nrCol'', nrCol''']

        return $ do
            logRewrite "Window.FirstValue" q
            let winArgs     = (WinFirstValue $ Column 1, (FNPreceding offset))
                placeHolder = Constant $ VLInt 0xdeadbeef
                proj        = [placeHolder, placeHolder, Column 2, placeHolder]
            winNode <- insert $ UnOp (WinFun winArgs) $(v "q1")
            void $ replaceWithNew q $ UnOp (Project proj) winNode |])

inlineWinAggrProject :: VLRule BottomUpProps
inlineWinAggrProject q =
  $(dagPatMatch 'q "WinFun args (Project proj (q1))"
    [| do
        w <- vectorWidth <$> vectorTypeProp <$> properties $(v "q1")

        return $ do
            logRewrite "Window.RunningAggr.Project" q

            let (afun, frameSpec) = $(v "args")
                env               = zip [1..] $(v "proj")
                -- Inline column expressions from the projection into
                -- the window function.
                afun'             = mapWinFun (mergeExpr env) afun

                -- WinAggr /adds/ the window function output to the
                -- input columns. We have to provide the schema of the
                -- input projection to which the window function
                -- output is added.
                proj' = $(v "proj") ++ [Column $ w + 1]

            winNode <- insert $ UnOp (WinFun (afun', frameSpec)) $(v "q1") 
            void $ replaceWithNew q $ UnOp (Project proj') winNode |])
