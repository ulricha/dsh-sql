{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Specialization and optimization of TA column expressions
module Database.DSH.Backend.Sql.Opt.Rewrite.Expr where

import           Control.Arrow
import           Control.Monad

import           Database.Algebra.Dag.Common
import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Rewrite.Common
import           Database.DSH.Common.Opt

{-# ANN module "HLint: ignore Reduce duplication" #-}

----------------------------------------------------------------------------------
-- Expression rewriting

pattern (:<=:) :: Expr -> Expr -> Expr
pattern e1 :<=: e2 <- BinAppE LtE e1 e2

pattern (:>=:) :: Expr -> Expr -> Expr
pattern e1 :>=: e2 <- BinAppE GtE e1 e2

pattern (:&&:) :: Expr -> Expr -> Expr
pattern e1 :&&: e2 = BinAppE And e1 e2

specializeExpr :: Expr -> Expr
specializeExpr e = case e of
    (e1 :>=: e2) :&&: (e1' :<=: e3) | e1 == e1' -> TernaryAppE Between e1 e2 e3
    (e1 :<=: e2) :&&: (e1' :>=: e3) | e1 == e1' -> TernaryAppE Between e1 e3 e2
    (e1 :<=: e2) :&&: ((e1' :>=: e3) :&&: e4) | e1 == e1' -> TernaryAppE Between e1 e3 e2 :&&: e4
    (e1 :>=: e2) :&&: ((e1' :<=: e3) :&&: e4) | e1 == e1' -> TernaryAppE Between e1 e2 e3 :&&: e4
    BinAppE f e1 e2 -> BinAppE f (specializeExpr e1) (specializeExpr e2)
    UnAppE f e1 -> UnAppE f (specializeExpr e1)
    ColE a -> ColE a
    ConstE val -> ConstE val
    TernaryAppE f e1 e2 e3 -> TernaryAppE f (specializeExpr e1) (specializeExpr e2) (specializeExpr e3)

----------------------------------------------------------------------------------
-- Plan rewriting

projectExpr :: TARule ()
projectExpr q =
  $(dagPatMatch 'q "Project ps (qi)"
    [| do
        let ps' = map (second specializeExpr) $(v "ps")
        predicate $ ps' /= $(v "ps")
        return $ do
            logRewrite "Basic.Expr.Project" q
            void $ replaceWithNew q $ UnOp (Project ps') $(v "qi") |])

selectExpr :: TARule ()
selectExpr q =
  $(dagPatMatch 'q "Select e (qi)"
    [| do
        let e' = specializeExpr $(v "e")
        predicate $ e' /= $(v "e")
        return $ do
            logRewrite "Basic.Expr.Project" q
            void $ replaceWithNew q $ UnOp (Select e') $(v "qi") |])
