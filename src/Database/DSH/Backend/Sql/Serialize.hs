{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ParallelListComp  #-}

-- | Insert 'Serialize' operators into table algebra plans.
module Database.DSH.Backend.Sql.Serialize
    ( insertSerialize
    ) where

import           Control.Monad.State
import           Data.Maybe

import qualified Database.Algebra.Dag.Build             as B
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang            as TA

import           Database.DSH.Backend.Sql.Vector
import           Database.DSH.Backend.Sql.VectorAlgebra ()
import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL

type TAVecBuild a = VecBuild TA.TableAlgebra
                             (DVec TA.TableAlgebra)
                             (RVec TA.TableAlgebra)
                             (KVec TA.TableAlgebra)
                             (FVec TA.TableAlgebra)
                             (SVec TA.TableAlgebra)
                             a

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define key, ref
-- and order columns as well as the required payload columns. 'insertSerialize'
-- decides whether key, ref and order columns are actually needed based on the
-- position of the vector in a shape or layout.
insertSerialize :: TAVecBuild (Shape (DVec TA.TableAlgebra))
                -> TAVecBuild (Shape (DVec TA.TableAlgebra))
insertSerialize g = g >>= traverseShape

traverseShape :: Shape TADVec -> TAVecBuild (Shape TADVec)
traverseShape (VShape dvec lyt) = do
    mLyt' <- traverseLayout lyt
    case mLyt' of
        Just lyt' -> do
            dvec' <- insertOp dvec noRef needKey needOrd
            return $ VShape dvec' lyt'
        Nothing   -> do
            dvec' <- insertOp dvec noRef noKey needOrd
            return $ VShape dvec' lyt

traverseShape (SShape dvec lyt)     = do
    mLyt' <- traverseLayout lyt
    case mLyt' of
        Just lyt' -> do
            dvec' <- insertOp dvec noRef needKey noOrd
            return $ SShape dvec' lyt'
        Nothing   -> do
            dvec' <- insertOp dvec noRef noKey noOrd
            return $ SShape dvec' lyt

traverseLayout :: Layout TADVec -> TAVecBuild (Maybe (Layout TADVec))
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
insertOp :: TADVec
         -> (VecRef -> VecRef)
         -> (VecKey -> VecKey)
         -> (VecOrder -> VecOrder)
         -> TAVecBuild TADVec
insertOp (TADVec q o k r i) updateRef updateKey updateOrd = do
    let o' = updateOrd o
        k' = updateKey k
        r' = updateRef r
    let op = TA.Serialize (mkRef r', mkKey k', mkOrd o', mkItems i)

    qp   <- lift $ B.insert $ UnOp op q
    return $ TADVec qp o' k' r' i

--------------------------------------------------------------------------------
-- Declaring need for key, ref and ord columns.

needRef :: VecRef -> VecRef
needRef = id

noRef :: VecRef -> VecRef
noRef = const (VecRef 0)

needOrd :: VecOrder -> VecOrder
needOrd = id

noOrd :: VecOrder -> VecOrder
noOrd = const (VecOrder [])

needKey :: VecKey -> VecKey
needKey = id

noKey :: VecKey -> VecKey
noKey = const (VecKey 0)

--------------------------------------------------------------------------------
-- Creating actual columns from vector meta data

mkRef :: VecRef -> [TA.RefCol]
mkRef (VecRef 0) = []
mkRef (VecRef i) = [ TA.RefCol (rc c) (TA.ColE $ rc c) | c <- [1..i] ]

mkOrd :: VecOrder -> [TA.OrdCol]
mkOrd (VecOrder ds) = [ TA.OrdCol (oc i, d) (TA.ColE $ oc i)
                      | i <- [1..] | d <- ds
                      ]

mkKey :: VecKey -> [TA.KeyCol]
mkKey (VecKey i) = [ TA.KeyCol (kc c) (TA.ColE $ kc c) | c <- [1..i] ]

mkItems :: VecItems -> [TA.PayloadCol]
mkItems (VecItems 0) = []
mkItems (VecItems i) = [ TA.PayloadCol (ic c) (TA.ColE $ ic c) | c <- [1..i] ]
