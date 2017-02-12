{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE FlexibleContexts  #-}

-- | Insert 'Serialize' operators for plans with composite keys into table
-- algebra plans.
module Database.DSH.Backend.Sql.Serialize
    ( insertSerialize
    ) where

import           Data.Maybe
import           Control.Monad.State

import qualified Database.Algebra.Dag.Build               as B
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang              as TA

-- import           Database.DSH.Backend.Sql.Relational.Natural ()
import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Common.QueryPlan

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define key, ref
-- and order columns as well as the required payload columns. 'insertSerialize'
-- decides whether key, ref and order columns are actually needed based on the
-- position of the vector in a shape or layout.
insertSerialize :: MonadState (B.BuildState TA.TableAlgebra) m => Shape TADVec -> m (Shape TADVec)
insertSerialize shape = traverseShape shape

traverseShape :: MonadState (B.BuildState TA.TableAlgebra) m => Shape TADVec -> m (Shape TADVec)
traverseShape (VShape dvec lyt) = do
    mLyt' <- traverseLayout lyt
    case mLyt' of
        Just lyt' -> do
            dvec' <- insertOp dvec noRef needKey needOrd
            return $ VShape dvec' lyt'
        Nothing   -> do
            dvec' <- insertOp dvec noRef noKey needOrd
            return $ VShape dvec' lyt

traverseLayout :: MonadState (B.BuildState TA.TableAlgebra) m => Layout TADVec -> m (Maybe (Layout TADVec))
traverseLayout LCol          = return Nothing
traverseLayout (LTuple lyts) = do
    mLyts <- mapM traverseLayout lyts
    if all isNothing mLyts
        then return Nothing
        else return $ Just $ LTuple $ zipWith fromMaybe lyts mLyts
traverseLayout (LNest dvec lyt) = do
    mLyt' <- traverseLayout lyt
    case mLyt' of
        Just lyt' -> do
            dvec' <- insertOp dvec needRef needKey needOrd
            return $ Just $ LNest dvec' lyt'
        Nothing   -> do
            dvec' <- insertOp dvec needRef noKey needOrd
            return $ Just $ LNest dvec' lyt

-- | Insert a Serialize node for the given vector
insertOp :: MonadState (B.BuildState TA.TableAlgebra) m
         => TADVec
         -> (VecRef -> VecRef)
         -> (VecKey -> VecKey)
         -> (VecOrder -> VecOrder)
         -> m TADVec
insertOp (TADVec q o k r i) updateRef updateKey updateOrd = do
    let o' = updateOrd o
        k' = updateKey k
        r' = updateRef r
    let op = TA.Serialize (mkRef r', mkKey k', mkOrd o', mkItems i)

    qp   <- B.insert $ UnOp op q
    return $ TADVec qp o' k' r' i

--------------------------------------------------------------------------------
-- Declaring need for key, ref and ord columns.

needRef :: VecRef -> VecRef
needRef = id

noRef :: VecRef -> VecRef
noRef = const (VecRef [])

needOrd :: VecOrder -> VecOrder
needOrd = id

needKey :: VecKey -> VecKey
needKey = id

noKey :: VecKey -> VecKey
noKey = const (VecKey [])

--------------------------------------------------------------------------------
-- Creating actual columns from vector meta data

mkRef :: VecRef -> [TA.RefCol]
mkRef (VecRef rs) = [ TA.RefCol c (TA.ColE c) | c <- rs ]

mkOrd :: VecOrder -> [TA.OrdCol]
mkOrd (VecOrder ds) = [ TA.OrdCol (c, d) (TA.ColE c)
                      | (c, d) <- ds
                      ]

mkKey :: VecKey -> [TA.KeyCol]
mkKey (VecKey ks) = [ TA.KeyCol c (TA.ColE c) | c <- ks ]

mkItems :: VecItems -> [TA.PayloadCol]
mkItems (VecItems is) = [ TA.PayloadCol c (TA.ColE c) | c <- is ]
