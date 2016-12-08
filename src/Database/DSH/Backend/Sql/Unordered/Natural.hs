{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Backend.Sql.Unordered.Natural
    (
    ) where

import           Control.Monad
import           Data.List.NonEmpty                            (NonEmpty ((:|)))
import           Data.Semigroup
import qualified Data.Sequence                                 as S

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Lang
import           Database.DSH.SL

import           Database.DSH.Backend.Sql.MultisetAlgebra.Lang
import           Database.DSH.Backend.Sql.Vector

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Vector-related expression constructors

unitSegId :: TExpr
unitSegId = TConstant UnitV

sngSegOrd :: TExpr
sngSegOrd = TConstant UnitV

plE :: TExpr -> TExpr
plE = TFourth

pl :: TExpr
pl = plE TInput

ordE :: TExpr -> TExpr
ordE = TThird

ord :: TExpr
ord = ordE TInput

keyE :: TExpr -> TExpr
keyE = TSecond

key :: TExpr
key = keyE TInput

segE :: TExpr -> TExpr
segE = TFirst

seg :: TExpr
seg = segE TInput

fromE :: TExpr -> TExpr
fromE = TFirst

from :: TExpr
from = fromE TInput

toE :: TExpr -> TExpr
toE = TFirst

--------------------------------------------------------------------------------
-- Join predicates for various index joins

-- Join predicate on outer indexes (s = s)
joinSegEq :: JoinPredicate TExpr
joinSegEq = singlePred $ JoinConjunct seg Eq seg

-- | Join predicate along an index link (k = s)
joinIdxEq :: JoinPredicate TExpr
joinIdxEq = singlePred $ JoinConjunct key Eq seg

-- | Join predicate for a mapping join
mapJoinEq :: JoinPredicate TExpr
mapJoinEq = singlePred $ JoinConjunct from Eq seg

-- | Join predicate for a filtering map join
fmapJoinEq :: JoinPredicate TExpr
fmapJoinEq = singlePred $ JoinConjunct TInput Eq seg

-- | Construct a result row for a multiset vector
dvecElem :: TExpr -> TExpr -> TExpr -> TExpr -> TExpr
dvecElem s k o p = TMkTuple $ s :| [k, o, p]

--------------------------------------------------------------------------------
--

-- | Construct a filtering map vector from the given expression.
filterMap :: TExpr -> AlgNode -> Build MA MAFVec
filterMap e n = MAFVec <$> project e n

-- | Construct a replication map that maps from 'f' to 't'
repMap :: TExpr -> TExpr -> AlgNode -> Build MA MARVec
repMap f t n = MARVec <$> project (tPair f t) n

-- | Construct a rekeying map that maps from 'f' to 't'
keyMap :: TExpr -> TExpr -> AlgNode -> Build MA MAKVec
keyMap f t n = MAKVec <$> project (tPair f t) n

-- | Convert a segment vector into a vector with uniform (i.e. integer) index
-- and order labels.
uniformVec :: ScalarVal -> AlgNode -> Build MA (MADVec, MAKVec)
uniformVec tag n = do
    qn <- rownum (tPair seg ord) n
    qs <- project (tPair TInpFirst (tPair (TConstant tag) TInpSecond)) qn
    m  <- keyMap (keyE TInpFirst) TInpSecond qs
    let s = plE TInpFirst
        k = TInpSecond
        o = TInpSecond
        i = plE TInpFirst
    qd <- project (dvecElem s k o i) qs
    pure (MADVec qd, m)

-- | Construct a value of a literal vector segment from the segment identifier,
-- the position, the value itself and a vector-unique inner index.
litSeg :: TExpr -> Int -> VecVal -> Int -> TExpr
litSeg s o v k = dvecElem s (TConstant $ IntV k) (TConstant $ IntV o) (valExpr v)

--------------------------------------------------------------------------------

instance SegmentAlgebra MA where
    type SLDVec MA = MADVec
    type SLRVec MA = MARVec
    type SLKVec MA = MAKVec
    type SLFVec MA = MAFVec
    type SLSVec MA = MASVec

    vecProject e (MADVec q) = do
        q' <- project (dvecElem seg key ord (mergeExpr pl e)) q
        pure $ MADVec q'

    vecSelect e (MADVec q) = do
        qd <- select (mergeExpr pl e) q
        m  <- filterMap key qd
        pure $ (MADVec qd, m)

    vecNumber (MADVec q) = MADVec <$> rownumPart seg ord q

    vecSegment (MADVec q) = MADVec <$> project (dvecElem key key ord pl) q

    vecUnsegment (MADVec q) = MADVec <$> project (dvecElem unitSegId key ord pl) q

    vecSort e (MADVec q) = do
        qd <- project (dvecElem seg key (tPair (mergeExpr pl e) ord) pl) q
        pure (MADVec qd, MASVec)

    vecAlign (MADVec q1) (MADVec q2) = do
        qj <- thetaJoin (singlePred $ JoinConjunct key Eq key) q1 q2
        let s = segE TInpFirst
            k = keyE TInpFirst
            o = ordE TInpFirst
            p = tPair (plE TInpFirst) (plE TInpSecond)
        qp <- project (dvecElem s k o p) qj
        pure $ MADVec qp

    vecSemiJoin pred (MADVec q1) (MADVec q2) = do
        qj <- semiJoin (joinSegEq <> (mergeExpr pl <$> pred)) q1 q2
        m  <- filterMap key qj
        pure (MADVec qj, m)

    vecAntiJoin pred (MADVec q1) (MADVec q2) = do
        qj <- antiJoin (joinSegEq <> (mergeExpr pl <$> pred)) q1 q2
        m  <- filterMap key qj
        pure (MADVec qj, m)

    vecThetaJoin pred (MADVec q1) (MADVec q2) = do
        let s = segE TInpFirst
            k = tPair (keyE TInpFirst) (keyE TInpSecond)
            o = tPair (ordE TInpFirst) (ordE TInpSecond)
            p = tPair (plE TInpFirst) (plE TInpSecond)

        qj <- thetaJoin (joinSegEq <> (mergeExpr pl <$> pred)) q1 q2
        qd <- project (dvecElem s k o p) qj
        m1 <- repMap (keyE TInpFirst) k qj
        m2 <- repMap (keyE TInpSecond) k qj

        pure (MADVec qd, m1, m2)

    vecCartProduct (MADVec q1) (MADVec q2) = do
        let s = segE TInpFirst
            k = tPair (keyE TInpFirst) (keyE TInpSecond)
            o = tPair (ordE TInpFirst) (ordE TInpSecond)
            p = tPair (plE TInpFirst) (plE TInpSecond)

        qj <- thetaJoin joinSegEq q1 q2
        qd <- project (dvecElem s k o p) qj
        m1 <- repMap (keyE TInpFirst) k qj
        m2 <- repMap (keyE TInpSecond) k qj

        pure (MADVec qd, m1, m2)

    vecNestJoin pred (MADVec q1) (MADVec q2) = do
        let s = keyE TInpFirst
            k = tPair (keyE TInpFirst) (keyE TInpSecond)
            o = ordE TInpSecond
            p = tPair (plE TInpFirst) (plE TInpSecond)

        qj <- thetaJoin (joinSegEq <> (mergeExpr pl <$> pred)) q1 q2
        qd <- project (dvecElem s k o p) qj
        m1 <- repMap (keyE TInpFirst) k qj
        m2 <- repMap (keyE TInpSecond) k qj

        pure (MADVec qd, m1, m2)

    vecGroup e (MADVec q) = do
        -- Pair input with grouping key
        q1 <- project (tPair TInput (mergeExpr pl e)) q
        -- Outer index and grouping key for the outer vector
        q2 <- project (tPair (segE TInpFirst) TInpSecond) q1
        -- Compute unique combinations of outer index and grouping key
        qk <- distinct q2
        -- schema for the outer vector
        let so = TInpFirst    -- original segments
            ko = TInput       -- grouping key + outer index
            oo = TInpSecond   -- grouping key
            po = TInpSecond   -- grouping key
        qo <- project (dvecElem so ko oo po) qk
        -- schema for the inner vector
        let si = tPair (segE TInpFirst) TInpSecond -- grouping key + outer index
            ki = keyE TInpFirst                    -- original index
            oi = ordE TInpFirst                    -- original order label
            pi = plE TInpFirst                     -- original payload
        qi <- project (dvecElem si ki oi pi) q1
        pure (MADVec qo, MADVec qi, MASVec)

    vecUnique (MADVec q) = do
        qn <- rownumPart (tPair seg pl) ord q
        qs <- select (TEq TInpSecond (TConstant (IntV 1))) qn
        qd <- project TInpFirst qs
        pure $ MADVec qd

    vecAppend (MADVec q1) (MADVec q2) = do
        (MADVec qu1, m1) <- uniformVec (IntV 1) q1
        (MADVec qu2, m2) <- uniformVec (IntV 2) q2
        qu               <- union qu1 qu2
        pure (MADVec qu, m1, m2)

    vecUnboxKey (MADVec q) = keyMap key seg q

    vecReplicateNest (MADVec qo) (MADVec qi) = do
        qj <- thetaJoin joinIdxEq qo qi
        let s = segE TInpSecond
            k = keyE TInpSecond
            o = ordE TInpSecond
            p = tPair (plE TInpFirst) (plE TInpSecond)
        qd <- project (dvecElem s k o p) qj
        m  <- repMap (keyE TInpFirst) (keyE TInpSecond) qj
        pure (MADVec qd, m)

    vecAppFilter (MAFVec qm) (MADVec q) = do
        qj <- semiJoin fmapJoinEq q qm
        m  <- filterMap key qj
        pure (MADVec qj, m)

    -- FIXME appkey should not need to produce a rekeying vector.
    vecAppKey (MAKVec qm) (MADVec q) = do
        qj <- thetaJoin mapJoinEq qm q
        let s = toE TInpFirst
            k = keyE TInpSecond
            o = ordE TInpSecond
            p = plE TInpSecond
        qd <- project (dvecElem s k o p) qj
        pure (MADVec qd, undefined)

    vecAppRep (MARVec qm) (MADVec q) = do
        qj <- thetaJoin mapJoinEq qm q
        let s = toE TInpFirst
            k = tPair (toE TInpFirst) (keyE TInpSecond)
            o = ordE TInpSecond
            p = plE TInpSecond
        qd <- project (dvecElem s k o p) qj
        m  <- repMap (keyE TInpSecond) k qj
        pure (MADVec qd, m)

    vecAppSort MASVec v = pure (v, MASVec)

    vecUnboxSng (MADVec qo) (MADVec qi) = do
        qj <- thetaJoin joinIdxEq qo qi
        let s = segE TInpFirst
            k = keyE TInpFirst
            o = ordE TInpFirst
            p = tPair (plE TInpFirst) (plE TInpSecond)
        qd <- project (dvecElem s k o p) qj
        m  <- keyMap (keyE TInpSecond) k qj
        pure (MADVec qd, m)

    vecUnboxDefault e (MADVec qo) (MADVec qi) = do
        qj <- leftOuterJoin joinIdxEq e pl qo qi
        let s = segE TInpFirst
            k = keyE TInpFirst
            o = ordE TInpFirst
            p = tPair (plE TInpFirst) TInpSecond
        qd <- project (dvecElem s k o p) qj
        pure $ MADVec qd

    vecReplicateVector (MADVec q1) (MADVec q2) = do
        qj <- cartProduct q1 q2
        let s = keyE TInpSecond
            k = tPair (keyE TInpSecond) (keyE TInpFirst)
            o = tPair (ordE TInpSecond) (ordE TInpFirst)
            p = plE TInpFirst
        qd <- project (dvecElem s k o p) qj
        m  <- repMap (keyE TInpFirst) k qj
        pure (MADVec qd, m)

    vecGroupAggr groupExpr aggrFuns (MADVec q) = do
        qa <- groupAggr (tPair seg (mergeExpr pl groupExpr)) (fmap (mergeExpr pl <$>) aggrFuns) q
        let s = TFirst TInpFirst
            k = TInpFirst
            o = TSecond TInpFirst
            p = tPair (TSecond TInpFirst) TInpSecond
        qd <- project (dvecElem s k o p) qa
        pure $ MADVec qd

    vecReplicateScalar (MADVec q1) (MADVec q2) = do
        qj <- cartProduct q1 q2
        let s = segE TInpSecond
            k = keyE TInpSecond
            o = ordE TInpSecond
            p = tPair (plE TInpFirst) (plE TInpSecond)
        qd <- project (dvecElem s k o p) qj
        m  <- repMap (keyE TInpFirst) k qj

        pure (MADVec qd, m)

    vecFold a (MADVec q) = do
        qg <- groupAggr seg (pure (mergeExpr pl <$> a)) q
        let s = TInpFirst
            k = TInpFirst
            o = sngSegOrd
            p = TInpSecond
        qd <- project (dvecElem s k o p) qg
        pure $ MADVec qd

    vecGroupJoin p as (MADVec q1) (MADVec q2) = do
        qj <- groupJoin (singlePred $ JoinConjunct key Eq key) (fmap (mergeExpr pl <$>) as) q1 q2
        let s = segE TInpFirst
            k = keyE TInpFirst
            o = ordE TInpFirst
            p = tPair (plE TInpFirst) TInpSecond
        qd <- project (dvecElem s k o p) qj
        pure $ MADVec qd

    vecLit _ (UnitSeg sd) = MADVec <$> (lit $ S.mapWithIndex (\i d -> litSeg unitSegId i d i) sd)
    vecLit _ (Segs sds) = MADVec <$> (lit tuples)
      where
        tuples = S.mapWithIndex (\i f -> f i)
                 $ join
                 $ S.mapWithIndex (\s sd -> S.mapWithIndex (\p d k -> litSeg (segId s) p d k) sd) sds
        segId  = TConstant . IntV

    vecTableRef tab schema = MADVec <$> tableRef tab tupTy schema
      where
        tupTy = PTupleT $ fmap (PScalarT . snd) $ tableCols schema

    vecWinFun = error "vecWinFun not implemented"
    vecReverse = error "vecReverse not implemented"
    vecZip = error "vecZip not implemented"
    vecCombine = error "vecCombine not implemented"
