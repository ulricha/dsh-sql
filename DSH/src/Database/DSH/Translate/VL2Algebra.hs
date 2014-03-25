{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.VL2Algebra(implementVectorOpsX100, implementVectorOpsPF) where

import           Data.List                                             (intercalate)
import qualified Data.IntMap                                           as IM
import qualified Data.Map                                              as M

import           Control.Monad.State
import           Control.Applicative

import           Database.Algebra.Pathfinder                           (PFAlgebra)
import qualified Database.Algebra.Pathfinder.Data.Algebra as TA
import           Database.Algebra.Pathfinder                           (initLoop)
import           Database.Algebra.X100.Data                            (X100Algebra)
import           Database.Algebra.X100.Data.Create                     (dummy)
import           Database.Algebra.Dag                                  (AlgebraDag, nodeMap)
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common                           hiding (BinOp)
import qualified Database.Algebra.Dag.Common                           as C
import           Database.DSH.VL.Lang                              hiding (DBCol, Pair)
import qualified Database.DSH.VL.Lang                              as V

import           Database.DSH.Translate.FKL2VL              ()
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.VectorPrimitives
import           Database.DSH.VL.X100VectorPrimitives       ()
import           Database.DSH.VL.PathfinderVectorPrimitives ()

import           Database.DSH.Common.QueryPlan

type G alg = StateT (M.Map AlgNode Res) (GraphM () alg)

runG :: VectorAlgebra a => a -> G a r -> AlgPlan a r
runG i c = runGraph i $ fst <$> runStateT c M.empty

data Res = Prop    AlgNode
         | Rename  AlgNode
         | RDVec   AlgNode [DBCol]
         | RPair   Res Res
         | RTriple Res Res Res
         deriving Show

fromDict :: VectorAlgebra a => AlgNode -> G a (Maybe Res)
fromDict n = do
    dict <- get
    return $ M.lookup n dict

insertTranslation :: VectorAlgebra a => AlgNode -> Res -> G a ()
insertTranslation n res = modify (M.insert n res)

fromProp :: PVec -> Res
fromProp (PVec p) = Prop p

toProp :: Res -> PVec
toProp (Prop p) = PVec p
toProp _       = error "toProp: Not a prop vector"

fromRenameVector :: RVec -> Res
fromRenameVector (RVec r) = Rename r

toRenameVector :: Res -> RVec
toRenameVector (Rename r) = RVec r
toRenameVector _          = error "toRenameVector: Not a rename vector"

fromDVec :: DVec -> Res
fromDVec (DVec n cs) = RDVec n cs

toDVec :: Res -> DVec
toDVec (RDVec n cs) = DVec n cs
toDVec _            = error "toDVec: Not a DVec"

refreshLyt :: VectorAlgebra a => (TopLayout DVec) -> G a (TopLayout DVec)
refreshLyt l@(InColumn _) = return l
refreshLyt (Nest (DVec n _) lyt) = do
    Just n' <- fromDict n
    lyt'    <- refreshLyt lyt
    return $ Nest (toDVec n') lyt'
refreshLyt (Pair l1 l2) = do
    l1' <- refreshLyt l1
    l2' <- refreshLyt l2
    return $ Pair l1' l2'

refreshShape :: VectorAlgebra a => (TopShape DVec) -> G a (TopShape DVec)
refreshShape (ValueVector (DVec n _) lyt) = do
    v <- fromDict n
    case v of
        Just n' -> do
            lyt' <- refreshLyt lyt
            return $ ValueVector (toDVec n') lyt'
        _ -> error $ "Disaster: " ++ show v
refreshShape (PrimVal (DVec n _) lyt) = do
    v <- fromDict n
    case v of
        Just (RDVec n' cs) -> do
            lyt'              <- refreshLyt lyt
            return $ PrimVal (DVec n' cs) lyt'
        x -> error $ show x

translate :: VectorAlgebra a => NodeMap VL -> AlgNode -> G a Res
translate vlNodes n = do
    r <- fromDict n

    case r of
        -- The VL node has already been encountered and translated.
        Just res -> return $ res

        -- The VL node has not been translated yet.
        Nothing  -> do
            let vlOp = getVL n vlNodes
            r' <- case vlOp of
                TerOp t c1 c2 c3 -> do
                    c1' <- translate vlNodes c1 
                    c2' <- translate vlNodes c2 
                    c3' <- translate vlNodes c3
                    lift $ translateTerOp t c1' c2' c3'
                C.BinOp b c1 c2    -> do
                    c1' <- translate vlNodes c1
                    c2' <- translate vlNodes c2
                    lift $ translateBinOp b c1' c2'
                UnOp u c1        -> do
                    c1' <- translate vlNodes c1
                    lift $ translateUnOp u c1'
                NullaryOp o      -> lift $ translateNullary o

            insertTranslation n r'
            return r'

getVL :: AlgNode -> NodeMap VL -> VL
getVL n vlNodes = case IM.lookup n vlNodes of
    Just op -> op
    Nothing -> error $ "getVL: node " ++ (show n) ++ " not in VL nodes map " ++ (pp vlNodes)

pp :: NodeMap VL -> String
pp m = intercalate ",\n" $ map show $ IM.toList m

vl2Algebra :: VectorAlgebra a => (NodeMap VL, TopShape DVec) -> G a (TopShape DVec)
vl2Algebra (vlNodes, plan) = do
    mapM_ (translate vlNodes) roots
    
    refreshShape plan
  where
    roots :: [AlgNode]
    roots = rootsFromTopShape plan

translateTerOp :: VectorAlgebra a => TerOp -> Res -> Res -> Res -> GraphM () a Res
translateTerOp t c1 c2 c3 = 
    case t of
        Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromRenameVector r1) (fromRenameVector r2)

translateBinOp :: VectorAlgebra a => V.BinOp -> Res -> Res -> GraphM () a Res
translateBinOp b c1 c2 = case b of
    GroupBy -> do
        (d, v, p) <- vecGroupBy (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec d) (fromDVec v) (fromProp p)

    Sort -> do
        (d, p) <- vecSort (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec d) (fromProp p)

    DistPrim -> do
        (v, p) <- vecDistPrim (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p)

    DistDesc -> do
        (v, p) <- vecDistDesc (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p)

    DistSeg -> do
        (v, p) <- vecDistSeg (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p)

    Align -> do
        (v, p) <- vecAlign (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p)

    PropRename -> fromDVec <$> vecPropRename (toRenameVector c1) (toDVec c2)

    PropFilter -> do
        (v, r) <- vecPropFilter (toRenameVector c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    PropReorder -> do
        (v, p) <- vecPropReorder (toProp c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p)

    Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRenameVector r1) (fromRenameVector r2)

    Restrict -> do
        (v, r) <- vecRestrict (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    BinExpr e -> fromDVec <$> vecBinExpr e (toDVec c1) (toDVec c2)

    AggrS a -> fromDVec <$> vecAggrS a (toDVec c1) (toDVec c2)

    AggrNonEmptyS a -> fromDVec <$> vecAggrNonEmptyS a (toDVec c1) (toDVec c2)

    SelectPos o -> do
        (v, r) <- selectPos (toDVec c1) o (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    SelectPosS o -> do
        (v, r) <- selectPosS (toDVec c1) o (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    Zip -> fromDVec <$> vecZip (toDVec c1) (toDVec c2)

    ZipS -> do
        (v, r1 ,r2) <- vecZipS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRenameVector r1) (fromRenameVector r2)

    CartProduct -> do
        (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)

    CartProductS -> do
        (v, p1, p2) <- vecCartProductS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)

    NestProductS -> do
        (v, p2) <- vecNestProductS (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p2)

    (EquiJoin e1 e2) -> do
        (v, p1, p2) <- vecEquiJoin e1 e2 (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)

    (EquiJoinS e1 e2) -> do
        (v, p1, p2) <- vecEquiJoinS e1 e2 (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromProp p1) (fromProp p2)

    (NestJoinS e1 e2) -> do
        (v, p2) <- vecNestJoinS e1 e2 (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromProp p2)

    (SemiJoin e1 e2) -> do
        (v, r) <- vecSemiJoin e1 e2 (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    (SemiJoinS e1 e2) -> do
        (v, r) <- vecSemiJoinS e1 e2 (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    (AntiJoin e1 e2) -> do
        (v, r) <- vecAntiJoin e1 e2 (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    (AntiJoinS e1 e2) -> do
        (v, r) <- vecAntiJoinS e1 e2 (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRenameVector r)

    TransposeS -> do
        (qo, qi) <- vecTransposeS (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec qo) (fromDVec qi)

-- singleton and only are just markers for the transition between
-- non-list values and lists with one element (representation of both
-- is the same).
singleton :: Res -> Res
singleton = id

only :: Res -> Res
only = id

translateUnOp :: VectorAlgebra a => UnOp -> Res -> GraphM () a Res
translateUnOp u c = case u of
    Singleton        -> return $ singleton c
    Only             -> return $ only c
    UniqueS          -> fromDVec <$> vecUniqueS (toDVec c)
    Number           -> fromDVec <$> vecNumber (toDVec c)
    NumberS          -> fromDVec <$> vecNumberS (toDVec c)
    DescToRename     -> fromRenameVector <$> descToRename (toDVec c)
    Segment          -> fromDVec <$> vecSegment (toDVec c)
    Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    Select e         -> fromDVec <$> vecSelect e (toDVec c)
    Aggr a           -> fromDVec <$> vecAggr a (toDVec c)
    AggrNonEmpty as  -> fromDVec <$> vecAggrNonEmpty as (toDVec c)
    SortSimple es -> do
        (d, p) <- vecSortSimple es (toDVec c)
        return $ RPair (fromDVec d) (fromProp p)
    GroupSimple es -> do
        (qo, qi, p) <- vecGroupSimple es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromProp p)
    Project cols -> fromDVec <$> vecProject cols (toDVec c)
    Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RPair (fromDVec d) (fromProp p)
    ReverseS      -> do
        (d, p) <- vecReverseS (toDVec c)
        return $ RPair (fromDVec d) (fromProp p)
    SelectPos1 op pos -> do
        (d, p) <- selectPos1 (toDVec c) op pos
        return $ RPair (fromDVec d) (fromRenameVector p)
    SelectPos1S op pos -> do
        (d, p) <- selectPos1S (toDVec c) op pos
        return $ RPair (fromDVec d) (fromRenameVector p)
    GroupAggr g as -> fromDVec <$> vecGroupAggr g as (toDVec c)

    Reshape n -> do
        (qo, qi) <- vecReshape n (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    ReshapeS n -> do
        (qo, qi) <- vecReshapeS n (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    Transpose -> do
        (qo, qi) <- vecTranspose (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    R1            -> case c of
        (RPair c1 _)     -> return c1
        (RTriple c1 _ _) -> return c1
        _                -> error "R1: Not a tuple"
    R2            -> case c of
        (RPair _ c2)     -> return c2
        (RTriple _ c2 _) -> return c2
        _                -> error "R2: Not a tuple"
    R3            -> case c of
        (RTriple _ _ c3) -> return c3
        _                -> error "R3: Not a tuple"

translateNullary :: VectorAlgebra a => NullOp -> GraphM () a Res
translateNullary SingletonDescr      = fromDVec <$> singletonDescr
translateNullary (Lit tys vals)      = fromDVec <$> vecLit tys vals
translateNullary (TableRef n tys hs) = fromDVec <$> vecTableRef n tys hs

-- | Insert SerializeRel operators in TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in DVec.
insertSerialize :: G PFAlgebra (TopShape DVec) -> G PFAlgebra (TopShape DVec)
insertSerialize g = g >>= traverseShape
  
  where 
    traverseShape :: TopShape DVec -> G PFAlgebra (TopShape DVec)
    traverseShape (ValueVector dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ ValueVector dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr needRelPos
                return $ ValueVector dvec' lyt
        
    traverseShape (PrimVal dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ PrimVal dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr noPos
                return $ PrimVal dvec' lyt
    
    traverseLayout :: (TopLayout DVec) -> G PFAlgebra (Maybe (TopLayout DVec))
    traverseLayout (InColumn _) = return Nothing
    traverseLayout (Pair lyt1 lyt2) = do
        mLyt1' <- traverseLayout lyt1
        mLyt2' <- traverseLayout lyt2
        case (mLyt1', mLyt2') of
            (Just lyt1', Just lyt2') -> return $ Just $ Pair lyt1' lyt2'
            (Just lyt1', Nothing)    -> return $ Just $ Pair lyt1' lyt2
            (Nothing, Just lyt2')    -> return $ Just $ Pair lyt1 lyt2'
            (Nothing, Nothing)       -> return Nothing
    traverseLayout (Nest dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec needDescr needAbsPos
                return $ Just $ Nest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needDescr needRelPos
                return $ Just $ Nest dvec' lyt

      
    -- | Insert a Serialize node for the given vector
    insertOp :: DVec -> Maybe TA.DescrCol -> TA.SerializeOrder -> G PFAlgebra DVec
    insertOp (DVec q cols) descr pos = do
        let cs = map (TA.PayloadCol . ("item" ++) . show) cols
            op = TA.Serialize (descr, pos, cs)

        qp   <- lift $ insertNode $ UnOp op q
        return $ DVec qp cols

    needDescr = Just (TA.DescrCol "descr")
    noDescr   = Nothing

    needAbsPos = TA.AbsPos "pos"
    needRelPos = TA.RelPos ["pos"]
    noPos      = TA.NoPos

implementVectorOpsX100 :: QueryPlan VL -> QueryPlan X100Algebra
implementVectorOpsX100 vlPlan = mkQueryPlan opMap shape tagMap
  where
    x100Plan               = vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan)
    (opMap, shape, tagMap) = runG dummy x100Plan

implementVectorOpsPF :: QueryPlan VL -> QueryPlan PFAlgebra
implementVectorOpsPF vlPlan = mkQueryPlan opMap shape tagMap
  where
    taPlan                 = vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan)
    serializedPlan         = insertSerialize taPlan
    (opMap, shape, tagMap) = runG initLoop serializedPlan
