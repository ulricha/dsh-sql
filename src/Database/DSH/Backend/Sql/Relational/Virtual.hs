{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ParallelListComp     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.Backend.Sql.Relational.Virtual
    (
    ) where

import qualified Data.Foldable                              as F
import           Data.List                                  (transpose)
import qualified Data.List.NonEmpty                         as N
import           Data.Monoid                                hiding (All, Any,
                                                             Sum)
import           GHC.Exts

import           Database.Algebra.Dag.Build
import           Database.Algebra.Table.Construct
import           Database.Algebra.Table.Lang

import qualified Database.DSH.Common.Lang                   as L
import qualified Database.DSH.VSL                           as VSL

import           Database.DSH.Backend.Sql.Relational.Common
import           Database.DSH.Backend.Sql.Vector

{-# ANN module "HLint: ignore Reduce duplication" #-}

segmentLookupPred :: VecRef -> VSL.SegmentLookup -> VSL.SegmentLookup -> [(Expr, Expr, JoinRel)]
segmentLookupPred (VecRef r) VSL.Direct VSL.Direct =
    [ (ColE $ rc c, ColE $ rc $ c + r, EqJ) | c <- [1..r] ]
segmentLookupPred (VecRef _) VSL.Direct VSL.Unit   = []
segmentLookupPred (VecRef _) VSL.Unit   VSL.Direct = []
segmentLookupPred (VecRef _) VSL.Unit   VSL.Unit   = []

identitySegMap :: TADVec -> Build TableAlgebra TARVec
identitySegMap (TADVec q _ (VecKey k) _ _) = TARVec <$> proj p q
                                                    <*> pure (VecTransSrc k)
                                                    <*> pure (VecTransDst k)
  where
    p  = identityMapProj (VecKey k)

instance VSL.VirtualSegmentAlgebra TableAlgebra where
    type VSLDVec TableAlgebra = TADVec
    type VSLRVec TableAlgebra = TARVec

    vecDistinct (TADVec q o k r i) = do
        -- Create per-segment groups based on the items and select the
        -- first member of each group
        qu <- projM (ordProj o ++ keyProj k ++ refProj r ++ itemProj i)
              $ selectM (BinAppE Eq (ColE soc) (ConstE $ VInt 1))
              $ rownum soc (ordCols o) (map ColE $ refCols r ++ itemCols i) q

        return $ TADVec qu o k r i

    -- FIXME we might have key order for inner vectors. include the
    -- key here.
    vecNumber (TADVec q o@(VecOrder ds) k r i) = do
        let i' = VecItems (unItems i + 1)
            nc = ic (unItems i + 1)

        qn <- rownum' nc
                      [ (ColE c, d) | c <- ordCols o | d <- ds ]
                      (map ColE (refCols r)) q
        return $ TADVec qn o k r i'

    -- FIXME does flipping the direction really implement reversing of
    -- the order?
    vecReverse (TADVec q (VecOrder ds) k r i) = do
        let o' = VecOrder $ map flipDir ds
        sortMap <- identitySegMap $ TADVec q (VecOrder ds) k r i
        return ( TADVec q o' k r i, sortMap)

    -- Implement per-segment sorting. Note that we use relative per-segment
    -- order and do not establish a global per-vector order of tuples.
    vecSort sortExprs (TADVec q o k r i) = do
        let o'       = VecOrder (map (const Asc) sortExprs) <> o
            -- Include the old order columns. This implements stable
            -- sorting and guarantees a strict total order of columns.
            sortCols = [ eP (oc c) (taExpr e) | c <- [1..] | e <- sortExprs ]
                       ++
                       [ mP (oc (c + length sortExprs)) (oc c)
                       | c <- [1..unOrd o]
                       ]

        qe <- proj (sortCols ++ keyProj k ++ refProj r ++ itemProj i) q
        sortMap <- identitySegMap $ TADVec q o k r i
        return ( TADVec qe o' k r i
               , sortMap
               )

    vecAggr as (TADVec q _ _ _ _) = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = VecRef 1
            i = VecItems (length as)

        let oneE = ConstE $ int 1
            acols = zipWith (\a c -> (aggrFun a, ic c)) (N.toList as) [1..]

        let mDefaultVals = zip (map snd acols) (map aggrFunDefault $ toList as)
        qa <- projM ([eP (oc 1) oneE, eP (kc 1) oneE, eP (rc 1) oneE] ++ map (cP . snd) acols)
              $ aggr acols [] q
        qd <- aggrDefault qa o k r mDefaultVals

        return $ TADVec qd o k r i

    vecAggrSeg a (TADVec qi _ _ r2 _) = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = r2
            i = VecItems 1

        -- Group the inner vector by ref.
        qa <- aggr [(aggrFun a, ic 1)] [ (c, ColE c) | c <- refCols r2 ] qi
        -- Add synthetic key and order columns (which will never be referenced).
        qn <- projM ([cP (oc 1), mP (kc 1) (oc 1)] ++ refProj r ++ itemProj i)
              $ rownum (oc 1) (refCols r) [] qa

        return $ TADVec qn o k r i

    vecGroup groupExprs (TADVec q o k r i) = do
        let gl = length groupExprs
        let o1 = VecOrder $ replicate gl Asc
            k1 = VecKey $ unRef r + gl
            r1 = r
            i1 = VecItems gl

        let o2 = o
            k2 = k
            r2 = VecRef $ unRef r + gl
            i2 = i

        -- Apply the grouping expressions
        let groupCols  = [ gc c | c <- [1..] | _ <- groupExprs ]
            groupProj  = [ eP g (taExpr ge) | g <- groupCols | ge <- groupExprs ]

        qg <- proj (vecProj o k r i ++ groupProj) q

        -- Generate the outer vector: one tuple per distinct values of
        -- the ref and grouping columns.
        let outerKeyProj = [ mP (kc c) g | c <- [1..] | g <- refCols r ++ groupCols ]
            outerOrdProj = [ mP (oc c) g | c <- [1..] | g <- groupCols ]
            outerItemProj = [ mP (ic c) g | c <- [1..] | g <- groupCols ]

        qo <- projM (outerOrdProj ++ outerKeyProj ++ refProj r ++ outerItemProj)
              $ distinctM
              $ proj (refProj r ++ [ cP g | g <- groupCols ]) qg

        -- Generate the inner vector that references the groups in the
        -- outer vector.
        let innerRefProj = [ mP (rc c) g | c <- [1..] | g <- refCols r ++ groupCols ]
        qi <- proj (ordProj o ++ keyProj k ++ innerRefProj ++ itemProj i) qg

        sortMap <- identitySegMap $ TADVec q o k r i

        return ( TADVec qo o1 k1 r1 i1
               , TADVec qi o2 k2 r2 i2
               , sortMap
               )

    vecAlign (TADVec q1 o1 k1 r1 i1) (TADVec q2 _ k2 _ i2) = do
        -- Join both vectors by their keys. Because this is a
        -- 1:1-join, we can discard order and ref of the right input.
        qa <- projM (ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj (i1 <> i2))
              $ thetaJoinM (keyJoin k1 k2)
                    (return q1)
                    (proj (shiftKey k1 k2 ++ shiftItems i1 i2) q2)
        return $ TADVec qa o1 k1 r1 (i1 <> i2)

    vecZip (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 r2 i2) = do
        let -- The result vector uses synthetic rownum-generated
            -- per-segment order. As key, we can simply use the key
            -- from either left or right side. Both will retain their
            -- key property as we are doing a 1:1 join.
            o = VecOrder [Asc]
            k = k1
            r = r1
            i = i1 <> i2

        qj <- thetaJoinM ( (ColE lsoc, ColE rsoc, EqJ) : refJoinPred r1)
                  (rownum' lsoc (synthOrder o1) (map ColE $ refCols r1) q1)
                  (projM ([cP rsoc] ++ shiftKey k1 k2 ++ shiftRef r1 r2 ++ shiftItems i1 i2)
                   $ rownum' rsoc (synthOrder o2) (map ColE $ refCols r2) q2)

        let keyProj1 = [ mP (dc c) (kc c) | c <- [1..unKey k1] ]
                       ++
                       [ mP (sc c) (kc c) | c <- [1..unKey k1] ]
            keyProj2 = [ mP (dc c) (kc c) | c <- [1..unKey k1] ]
                       ++
                       [ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]

        qk1 <- proj keyProj1 qj
        qk2 <- proj keyProj2 qj
        qd  <- proj ([mP (oc 1) lsoc] ++ keyProj k ++ refProj r1 ++ itemProj i) qj

        return ( TADVec qd o k r i
               , TARVec qk1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k1)
               , TARVec qk2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k1)
               )

    vecProject exprs (TADVec q o k r _) = do
        let items = zipWith (\c e -> eP (ic c) (taExpr e)) [1..] exprs
        qp <- proj (ordProj o ++ keyProj k ++ refProj r ++ items) q
        return $ TADVec qp o k r (VecItems $ length items)

    vecTableRef tableName schema = do
        q <- projM (baseKeyProj ++ baseOrdProj ++ baseItemProj ++ baseRefProj)
             $ dbTable tableName taColumns taKeys
        return $ TADVec q order key ref items

      where
        -- Columns and keys for the TA table operator
        taColumns = [ (c, algTy t)
                    | (L.ColName c, t) <- N.toList $ L.tableCols schema
                    ]

        taKeys =    [ Key [ c | L.ColName c <- N.toList k ]
                    | L.Key k <- N.toList $ L.tableKeys schema
                    ]

        -- We choose one key heuristically and use it to induce order.
        baseKeyCols  = chooseBaseKey (L.tableKeys schema)
        (baseKeyProj, baseOrdProj)
                     = unzip [ (mP (kc i) c, mP (oc i) c)
                             | i <- [1..]
                             | c <- N.toList baseKeyCols
                             ]
        baseItemProj = [ mP (ic i) c | i <- [1..] | (c, _) <- taColumns ]
        baseRefProj  = [ eP (rc 1) (ConstE $ int 1) ]

        items = VecItems $ N.length $ L.tableCols schema
        order = VecOrder $ const Asc <$> N.toList baseKeyCols
        key   = VecKey $ N.length baseKeyCols
        ref   = VecRef 1

    vecLit tys frame segments = do
        let o = VecOrder [Asc]
            k = VecKey 1
            r = VecRef 1
            i = VecItems (length tys)

        let refCol = mkRefCol segments
            keyCol = map (L.IntV . snd) $ zip refCol [1..]
            -- The schema for a vector literal consists of key and ref columns
            -- and all payload columns.
            litSchema = [(rc 1, intT), (kc 1, intT)]
                        ++
                        [ (ic c, algTy t) | c <- [1..] | t <- tys ]
            cols   = refCol : keyCol : map F.toList (VSL.vectorCols tys segments)
            rows   = transpose cols

        qr <- projM ([mP (oc 1) (kc 1), cP (kc 1), cP (rc 1)] ++ itemProj i)
              $ litTable' (map (map algVal) rows) litSchema
        return $ TADVec qr o k r i

      where
        -- Create a ref column with the proper length from the segment
        -- description.
        mkRefCol (VSL.UnitSeg _) = replicate (VSL.frameLen frame) (L.IntV 1)
        -- For a vector with multiple segments, we enumerate the segments to get
        -- segment identifiers and replicate those according to the length of
        -- the segment. Note that segments also contain empty segments, i.e.
        -- every segment identifier is obtained from the list of segments and
        -- matches the key in the outer vector.
        mkRefCol (VSL.Segs segs) = concat [ replicate (VSL.segLen s) (L.IntV si)
                                          | (s, si) <- zip segs [1..]
                                          ]

    vecAppend (TADVec q1 o1 k1 r1 i1) (TADVec q2 o2 k2 r2 i2) = do
        -- We have to use synthetic rownum-generated order and keys
        -- because left and right inputs might have non-compapible
        -- order and keys.

        -- Create synthetic order keys based on the original order
        -- columns and a marker column for left and right
        -- inputs. Order for inner vectors might not be key
        -- (per-segment order), so we have to include the key here to
        -- avoid random results.
        qs1 <- projM ([eP usc (ConstE $ VInt 1), cP soc]
                      ++ ordProj o1 ++ keyProj k1 ++ refProj r1 ++ itemProj i1)
               $ rownum' soc
                         (synthOrder o1 ++ map (\c -> (ColE c, Asc)) (keyCols k1))
                         []
                         q1

        -- Generate a rekeying vector that maps old keys to
        qk1 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k1) qs1

        -- Generate the union input for the left side: We use the
        -- marker column together with the rownum-generated values as
        -- order and keys.
        qu1 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 1) usc, mP (kc 2) soc]
                     ++ refProj r1 ++ itemProj i1)
                    qs1

        -- Do the same for the right input.
        qs2 <- projM ([eP usc (ConstE $ VInt 2), cP soc]
                      ++ ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i2)
               $ rownum' soc
                         (synthOrder o2 ++ map (\c -> (ColE c, Asc)) (keyCols k2))
                         []
                         q2
        qk2 <- proj ([mP (dc 1) usc, mP (dc 2) soc]
                     ++
                     keySrcProj k2) qs2

        qu2 <- proj ([mP (oc 1) usc, mP (oc 2) soc, mP (kc 2) usc, mP (kc 2) soc]
                     ++ refProj r2 ++ itemProj i2)
                    qs2

        -- With synthetic order and key values, both inputs are
        -- schema-compatible and can be used in a union.
        qu <- qu1 `union` qu2

        return ( TADVec qu (VecOrder [Asc, Asc]) (VecKey 2) r1 i1
               , TARVec qk1 (VecTransSrc $ unKey k1) (VecTransDst 2)
               , TARVec qk2 (VecTransSrc $ unKey k2) (VecTransDst 2)
               )

    -- FIXME can we really rely on keys being aligned/compatible?
    vecCombine (TADVec qb ob kb rb _)
               (TADVec q1 _ k1 _ i1)
               (TADVec q2 _ k2 _ i2) = do

        d1  <- thetaJoinM [ (ColE $ kc c, ColE $ kc $ c + unKey kb, EqJ)
                          | c <- [1..unKey k1]
                          ]
                   (projM (ordProj ob ++ keyProj kb ++ refProj rb)
                    $ select (ColE (ic 1)) qb)
                   (proj (shiftKey kb k1 ++ itemProj i1) q1)

        d2  <- thetaJoinM [ (ColE $ kc c, ColE $ kc $ c + unKey kb, EqJ)
                          | c <- [1..unKey k2]
                          ]
                   (projM (ordProj ob ++ keyProj kb ++ refProj rb)
                    $ select (UnAppE Not (ColE (ic 1))) qb)
                   (proj (shiftKey kb k2 ++ itemProj i2) q2)

        qu  <- unionM
                   (proj (ordProj ob ++ keyProj kb ++ refProj rb ++ itemProj i1) d1)
                   (proj (ordProj ob ++ keyProj kb ++ refProj rb ++ itemProj i2) d2)

        qk1 <- proj ([ mP (sc c) (kc $ c + unKey kb) | c <- [1..unKey k1] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey kb] ])
                    d1

        qk2 <- proj ([ mP (sc c) (kc $ c + unKey kb) | c <- [1..unKey k2] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey kb] ])
                    d2

        return ( TADVec qu ob kb rb i1
               , TARVec qk1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey kb)
               , TARVec qk2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey kb)
               )

    vecUpdateMap (TARVec qr1 s1 d1) (TARVec qr2 s2 d2) = do
        let s = s1
            d = d2

        -- Join maps on the left destination and right source columns to form
        -- the composition of the maps. Shift column names to avoid collisions
        -- of the right input to avoid collisions.
        qj <- projM (srcProj s1 ++ [ mP (dc c) (dc $ c + unDst d1) | c <- [1..unDst d2] ])
              $ thetaJoinM [ (ColE $ dc c, ColE $ sc $ c + unSrc s1, EqJ) | c <- [1..unDst d1] ]
                    (return qr1)
                    (proj (shiftSrc s1 s2 ++ shiftDst d1 d2) qr2)

        return $ TARVec qj s d

    vecMaterialize (TARVec qr s d) (TADVec q o k r i) = do
        let o' = o
            k' = k <> (VecKey $ unDst d)
            r' = VecRef $ unDst d
            i' = i

        let s' = VecTransSrc $ unKey k
            d' = VecTransDst $ unKey k'

        let repPred = [ (ColE c1, ColE c2, EqJ)
                      | c1 <- refCols r
                      | c2 <- srcCols s
                      ]
        qj  <- thetaJoin repPred q qr

        let newKeyProj = keyProj k
                         ++
                         [ mP (kc $ c + unKey k) (dc c)
                         | c <- [1..unDst d]
                         ]
            newRefProj = [ mP (rc c) (dc c) | c <- [1..unDst d] ]
        qd  <- proj (ordProj o' ++ newKeyProj ++ newRefProj ++ itemProj i)  qj
        qr' <- proj ([ mP (sc c) (kc c) | c <- [1..unKey k] ]
                     ++
                     [ mP (dc c) (kc c) | c <- [1..unKey k'] ])
                    qd


        return ( TADVec qd o' k' r' i'
               , TARVec qr' s' d'
               )

    vecMergeMap (TADVec q _ k r _) = do
        let mapSrcProj = [ mP (sc c) (kc c) | c <- [1..unKey k] ]
            mapDstProj = [ mP (dc c) (rc c) | c <- [1..unRef r] ]

        qk <- proj (mapSrcProj ++ mapDstProj) q
        return $ TARVec qk (VecTransSrc $ unKey k) (VecTransDst $ unRef r)

    vecSegment (TADVec q o k _ i) = do
        let mapRefProj = [ mP (rc c) (kc c) | c <- [1..unKey k]]
        qi <- proj (ordProj o ++ keyProj k ++ mapRefProj ++ itemProj i) q
        return $ TADVec qi o k (VecRef $ unKey k) i

    vecUnsegment (TADVec q o k r i) = do
        -- In general, we keep only per-segment order. The order of segments
        -- themselves is defined by the order of references. If a vector's
        -- segment structure is changed by *merging* vectors, we have to keep
        -- the order stable: Here, we add the references of the original vector
        -- to the order columns.
        let ro = VecOrder $ map (const Asc) [1..unRef r]
            o' = ro <> o
        let constRefProj = [ eP (rc 1) (ConstE $ int 1) ]
            combOrdCols  = [ mP (oc c) (rc c) | c <- [1..unOrd ro] ] ++ shiftOrd ro o
        qi <- proj (combOrdCols ++ keyProj k ++ constRefProj ++ itemProj i) q
        return $ TADVec qi o' k (VecRef 1) i

    vecNest (TADVec q o k _ i) = do
        qo <- litTable' [[int 1, int 1, int 1]] [(oc 1, intT), (kc 1, intT), (rc 1, intT)]
        let constRef = [eP (rc 1) (ConstE (int 1))]
        qi <- proj (ordProj o ++ keyProj k ++ constRef ++ itemProj i) q
        return ( TADVec qo (VecOrder [Asc]) (VecKey 1) (VecRef 1) (VecItems 0)
               , TADVec qi o k (VecRef 1) i
               )

    vecUnboxSng v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ k2 _ i2) = do
        let o = o1
            k = k1
            r = r1
            i = i1 <> i2

        qj <- thetaJoinM [ (ColE $ kc c, ColE $ rc $ c + unRef r1, EqJ)
                         | c <- [1..unKey k]
                         ]
                   (return q1)
                   (proj (shiftAll v1 v2) q2)

        qv <- proj (vecProj o k r i) qj
        qk <- proj ([ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k1] ])
                   qj

        return ( TADVec qv o k r i
               , TARVec qk (VecTransSrc $ unKey k2) (VecTransDst $ unKey k1)
               )

    vecUnboxDefault defaultValues v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ k2 _ i2) = do
        let o = o1
            k = k1
            r = r1
            i = i1 <> i2

        qj <- leftOuterJoinM [ (ColE $ kc c, ColE $ rc $ c + unRef r1, EqJ)
                             | c <- [1..unKey k]
                             ]
                   (return q1)
                   (proj (shiftAll v1 v2) q2)
        let defaultProj = [ eP (ic si) (BinAppE Coalesce (ColE $ ic si) (ConstE $ algVal v))
                          | i <- [1..unItems i2], let si = i + unItems i1
                          | v <- N.toList defaultValues
                          ]
        qd <- proj (ordProj o ++ keyProj k ++ refProj r ++ defaultProj) qj

        qv <- proj (vecProj o k r i) qj
        qk <- proj ([ mP (sc c) (kc $ c + unKey k1) | c <- [1..unKey k2] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k1] ])
                   qj

        return ( TADVec qv o k r i
               , TARVec qk (VecTransSrc $ unKey k2) (VecTransDst $ unKey k1)
               )

    vecReplicateScalar (TADVec q1 _ k1 _ i1) (TADVec q2 o2 k2 r2 i2) = do
        let o = o2
            k = k2
            r = r2
            i = i1 <> i2

            s = VecTransSrc $ unKey k1
            d = VecTransDst $ unKey k2

        qp <- crossM
                  (proj (shiftKey k2 k1 ++ itemProj i1) q1)
                  (proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ shiftItems i1 i2) q2)

        qd <- proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i) qp
        qr <- proj ([ mP (sc c) (kc $ c + unKey k2) | c <- [1..unKey k1] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k2] ])
                   qp

        return ( TADVec qd o k r i
               , TARVec qr s d
               )

    vecReplicateSeg (TADVec q1 _ k1 _ i1) (TADVec q2 o2 k2 r2 i2) = do
        let o = o2
            k = k2
            r = r2
            i = i1 <> i2

            s = VecTransSrc $ unKey k1
            d = VecTransDst $ unKey k2

        qj <- thetaJoinM [ (ColE (kc $ c + unKey k2), ColE (rc c), EqJ)
                         | c <- [1..unRef r2]
                         ]
                   (proj (shiftKey k2 k1 ++ itemProj i1) q1)
                   (proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ shiftItems i1 i2) q2)

        qd <- proj (ordProj o2 ++ keyProj k2 ++ refProj r2 ++ itemProj i) qj
        qr <- proj ([ mP (sc c) (kc $ c + unKey k2) | c <- [1..unKey k1] ]
                    ++
                    [ mP (dc c) (kc c) | c <- [1..unKey k2] ])
                   qj

        return ( TADVec qd o k r i
               , TARVec qr s d
               )

    vecUnitMap (TADVec q1 o1 k1 r1 i1) = do
        qm <- proj (keySrcProj k1 ++ [eP (dc 1) (ConstE unitSegId)]) q1
        return $ TARVec qm (VecTransSrc $ unKey k1) (VecTransDst 1)

    vecUpdateUnit (TARVec q1 s d) = do
        qm <- proj (srcProj s ++ [ eP (dc 1) (ConstE unitSegId) ]) q1
        return $ TARVec qm s (VecTransDst 1)

    vecSelect expr (TADVec q o k r i) = do
        qs <- select (taExpr expr) q
        qr <- proj (filterProj k) qs
        filterMap <- identitySegMap (TADVec q o k r i)
        return ( TADVec qs o k r i
               , filterMap
               )

    -- Group and aggregate each segment individually
    vecGroupAggr groupExprs aggrFuns (TADVec q _ _ r _) = do
        let gl = length groupExprs

        let -- Under the per-segment order regime, we need to specify the order for
            -- each segment of the input individually. Therefore, we can use the
            -- grouping keys for each segment.
            o' = VecOrder $ replicate gl Asc

            -- Grouping keys are keys for each individual segment. By combining
            -- them with segment identifiers, we obtain a key that is valid for
            -- the complete vector.
            k' = VecKey $ unRef r + gl

            -- We keep the segment structure of the original input vector.
            r' = r

            i' = VecItems $ length groupExprs + N.length aggrFuns

        let parts = [ cP (rc c) | c <- [1..unRef r] ]
                    ++
                    [ eP (ic c) (taExpr e) | e <- groupExprs | c <- [1..] ]

            aggrs = [ (aggrFun a, ic i) | a <- N.toList aggrFuns | i <- [gl+1..] ]

        let ordProjs = [ mP (oc c) (ic c) | c <- [1..gl] ]
            keyProjs = [ mP (kc c) (rc c) | c <- [1..unRef r] ]
                       ++
                       [ mP (kc $ unRef r + c) (ic c) | c <- [1..gl] ]
            refProjs = [ cP (rc c) | c <- [1..unRef r] ]

        qa <- projM (ordProjs ++ keyProjs ++ refProjs ++ itemProj i')
              $ aggr aggrs parts q

        return $ TADVec qa o' k' r' i'

    vecNestJoin l1 l2 p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = keyRef k1  -- Nesting operator: left vector defines reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- thetaJoinM (segmentLookupPred r1 l1 l2 ++ joinPredicate i1 p)
                   (return q1)
                   (proj (shiftAll v1 v2) q2)

        qd  <- proj (ordProj o ++ keyProj k ++ keyRefProj k1 ++ itemProj i) qj
        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qd o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecThetaJoin l1 l2 p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = r1         -- The left vector defines the reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (vecProj o k r i)
               $ thetaJoinM (segmentLookupPred r1 l1 l2 ++ joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecCartProduct v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 o2 k2 _ i2) = do
        let o = o1 <> o2   -- New order is defined by both left and right
            k = k1 <> k2   -- New key is defined by both left and right
            r = r1         -- The left vector defines the reference
            i = i1 <> i2   -- We need items from left and right

        qj  <- projM (vecProj o k r i)
               $ thetaJoinM (refJoinPred r1)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        qp1 <- proj (prodTransProjLeft k1 k2) qj
        qp2 <- proj (prodTransProjRight k1 k2) qj

        return ( TADVec qj o k r i
               , TARVec qp1 (VecTransSrc $ unKey k1) (VecTransDst $ unKey k)
               , TARVec qp2 (VecTransSrc $ unKey k2) (VecTransDst $ unKey k)
               )

    vecSemiJoin l1 l2 p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1

        qj <- semiJoinM (segmentLookupPred r1 l1 l2 ++ joinPredicate i1 p)
                  (return q1)
                  (proj (shiftAll v1 v2) q2)

        qf <- proj (identityMapProj k1) qj

        return ( TADVec qj o k r i
               , TARVec qf (VecTransSrc $ unKey k1) (VecTransDst $ unKey k1)
               )

    vecAntiJoin l1 l2 p v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1

        qj <- antiJoinM (segmentLookupPred r1 l1 l2 ++ joinPredicate i1 p)
                    (return q1)
                    (proj (shiftAll v1 v2) q2)

        qf <- proj (identityMapProj k1) qj

        return ( TADVec qj o k r i
               , TARVec qf (VecTransSrc $ unKey k1) (VecTransDst $ unKey k1)
               )

    vecGroupJoin l1 l2 p (L.NE as) v1@(TADVec q1 o1 k1 r1 i1) v2@(TADVec q2 _ _ _ _) = do
        let o = o1
            k = k1
            r = r1
            i = i1 <> VecItems (length as)

        let acols     = [ ic (unItems i1 + c) | _ <- toList as | c <- [1..] ]
            groupCols = [ (c, ColE c)
                        | c <- keyCols k1 ++ ordCols o1 ++ refCols r1 ++ itemCols i1
                        ]

        let join = if any requiresOuterJoin as
                   then leftOuterJoinM
                   else thetaJoinM

        let taAggrs = zip (map (aggrFunGroupJoin (unKey k1 + 1)) $ toList as) acols

        qa  <- projM (ordProj o ++ keyProj k ++ refProj r1 ++ itemProj i)
               $ aggrM taAggrs groupCols
               $ join (segmentLookupPred r1 l1 l2 ++ joinPredicate i1 p)
                     (return q1)
                     (proj (shiftAll v1 v2) q2)

        -- Add the default value for empty groups if the aggregate supports it.
        -- Note that we do not need a default for AggrCount, since COUNT(e) will
        -- count the non-NULL entries only and produce the 0 directly.
        let mDefaultVals = zip acols (map aggrFunDefault $ toList as)
        qd <- groupJoinDefault qa o k r i1 mDefaultVals

        return $ TADVec qd o k r i
