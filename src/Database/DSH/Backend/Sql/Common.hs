{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Common
    ( SqlVector(..)
    , SqlCode(..)
    , generateSqlShape
    ) where

import           Data.Maybe

import qualified Database.Algebra.Dag            as D
import qualified Database.Algebra.Table.Lang     as TA

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan

import           Database.DSH.Backend.Sql.Vector

-- | An abstraction over SQL code for a particular system (e.g. PostgreSQL,
-- MonetDB, HyPer).
class SqlCode c where
    -- | Generate code from a table algebra DAG. Implementations provide a list
    -- of queries and an optional prelude which might set up shared temporary
    -- tables or indexing.
    genSqlCode :: D.AlgebraDag TA.TableAlgebra -> (Maybe c, [c])

-- | In a query shape, render each root node for the algebraic plan into a
-- separate PostgreSQL SQL query.
generateSqlShape :: SqlCode c => QueryPlan TA.TableAlgebra TADVec -> Shape (SqlVector c)
generateSqlShape taPlan = renderSql $ queryShape taPlan
  where
    roots                    = D.rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = genSqlCode (queryDag taPlan)
    nodeToQuery              = zip roots sqlQueries
    lookupNode n             = fromMaybe $impossible $ lookup n nodeToQuery

    -- We do not need order columns to reconstruct results: order information is
    -- encoded in the SQL queries' ORDER BY clause. We rely on the physical
    -- order of the result table.
    renderSql                = fmap (\(TADVec q _ k r i) -> SqlVector (lookupNode q) k r i)
