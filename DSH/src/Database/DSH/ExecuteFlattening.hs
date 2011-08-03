{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, ParallelListComp #-}
module Database.DSH.ExecuteFlattening where

import qualified Language.ParallelLang.DBPH as P
import Language.ParallelLang.FKL.Data.WorkUnits
import qualified Language.ParallelLang.Common.Data.Type as T
import Database.DSH.Data
import Database.HDBC
import Control.Exception (evaluate)
import Database.DSH.Data
import Data.Convertible
import Database.DSH.Impossible

import Data.List (foldl')

import Data.Maybe (fromJust)
import Control.Applicative ((<$>))
import Control.Monad(liftM)

data SQL a = SQL (P.Query P.SQL)

fromFType :: T.Type -> Type
fromFType (T.Var _) = $impossible
fromFType (T.Fn _ _)  = $impossible
fromFType (T.Int)   = IntegerT
fromFType (T.Bool)  = BoolT
fromFType (T.Double) = DoubleT
fromFType (T.String) = TextT
fromFType (T.Unit) = UnitT
fromFType (T.Tuple [e1, e2]) = TupleT (fromFType e1) (fromFType e2)  
fromFType (T.List t) = ListT (fromFType t)

retuple :: Type -> Type -> Norm -> Norm
retuple (TupleT t1 t2) (ListT (TupleT te1 te2)) (TupleN e1 e2 _) = zipN $ TupleN (retuple t1 (ListT te1) e1) (retuple t2 (ListT te2) e2) undefined
retuple t te n | t == te = n
               | otherwise = error $ "Don't know how to rewrite: " ++ show t ++ " into " ++ show te

zipN :: Norm -> Norm
zipN (TupleN (ListN es1 (ListT t1)) (ListN es2 (ListT t2)) _) = ListN [TupleN e1 e2 (TupleT t1 t2) | e1 <- es1 | e2 <- es2] (ListT (TupleT t1 t2))
zipN _ = $impossible

executeQuery :: forall a. forall conn. (QA a, IConnection conn) => conn -> ReconstructionPlan -> T.Type -> SQL a -> IO a
executeQuery c _ vt (SQL q) = do
                                let et = reify (undefined :: a)
                                let gt = fromFType vt
                                n <- makeNorm c q (fromFType vt)
                                return $ fromNorm $ retuple gt et $ fromEither (fromFType vt) n

makeNorm :: IConnection conn => conn -> P.Query P.SQL -> Type -> IO (Either Norm [(Int, Norm)])
makeNorm c (P.PrimVal (P.SQL _ s q)) t = do
                                          (r, d) <- doQuery c q
                                          let (iC, ri) = schemeToResult s d
                                          let [(_, [(_, v)])] = partByIter iC r
                                          let i = snd (fromJust ri)
                                          return $ Left $ normalise t i v
makeNorm c (P.ValueVector (P.SQL _ s q)) t = do
                                               (r, d) <- doQuery c q
                                               let (iC, ri) = schemeToResult s d
                                               let parted = partByIter iC r
                                               let i = snd (fromJust ri)
                                               return $ Right $ normaliseList t i parted
makeNorm c (P.TupleVector [q1, q2]) t@(TupleT t1 t2) = do
                                                         r1 <- liftM (fromEither t1) $ makeNorm c q1 t1
                                                         r2 <- liftM (fromEither t2) $ makeNorm c q2 t2
                                                         return $ Left $ TupleN r1 r2 t
makeNorm c (P.NestedVector (P.SQL _ s q) qr) t@(ListT t1) = do
                                                             (r, d) <- doQuery c q
                                                             let (iC, ri) = schemeToResult s d
                                                             let parted = partByIter iC r
                                                             inner <- (liftM fromRight) $ makeNorm c qr t1
                                                             return $ Right $ constructDescriptor t parted inner

fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight _         = error "fromRight"

fromEither :: Type -> Either Norm [(Int, Norm)] -> Norm
fromEither _ (Left n) = n
fromEither t (Right ns) = concatN t $ map snd ns 

constructDescriptor :: Type -> [(Int, [(Int, [SqlValue])])] -> [(Int, Norm)] -> [(Int, Norm)]
constructDescriptor t@(ListT t1) ((i, vs):outers) inners = let (r, inners') = nestList t1 (map fst vs) inners
                                                            in (i, ListN r t) : constructDescriptor t outers inners'
constructDescriptor _            []               _      = []

nestList :: Type -> [Int] -> [(Int, Norm)] -> ([Norm], [(Int, Norm)])
nestList t ps'@(p:ps) ls@((d,n):lists) | p == d = n `combine` (nestList t ps lists)
                                       | p <  d = ListN [] t `combine` (nestList t ps ls)
                                       | p >  d = nestList t ps' lists
nestList t (p:ps)     []                         = ListN [] t `combine` (nestList t ps [])
nestList t []         ls                         = ([], ls) 

combine :: Norm -> ([Norm], [(Int, Norm)]) -> ([Norm], [(Int, Norm)])
combine n (ns, r) = (n:ns, r)


concatN :: Type -> [Norm] -> Norm
concatN _ ns@((ListN ls t1):_) = foldl' (\(ListN e t) (ListN e1 _) -> ListN (e1 ++ e) t) (ListN [] t1) ns
concatN t []                   = ListN [] t
concatN _ _                    = error "concatN: Not a list of lists"

normaliseList :: Type -> Int -> [(Int, [(Int, [SqlValue])])] -> [(Int, Norm)]
normaliseList t@(ListT t1) c vs = reverse $ foldl' (\tl (i, v) -> (i, ListN (map ((normalise t1 c) . snd) v) t):tl) [] vs
normaliseList _            _ _  = error "normaliseList: Should not happen"

normalise :: Type -> Int -> [SqlValue] -> Norm
normalise UnitT _ _ = UnitN UnitT
normalise t i v = convert (v !! i, t)
                                                    
doQuery :: IConnection conn => conn -> String -> IO ([[SqlValue]], [(String, SqlColDesc)])
doQuery c q = do
                sth <- prepare c q
                _ <- execute sth []
                res <- dshFetchAllRowsStrict sth
                resDescr <- describeResult sth
                return (res, resDescr)
                
                
dshFetchAllRowsStrict :: Statement -> IO [[SqlValue]]
dshFetchAllRowsStrict stmt = go []
  where
  go :: [[SqlValue]] -> IO [[SqlValue]]
  go acc = do  mRow <- fetchRow stmt
               case mRow of
                 Nothing   -> return (reverse acc)
                 Just row  -> do mapM_ evaluate row
                                 go (row : acc)
                                 
partByIter :: Int -> [[SqlValue]] -> [(Int, [(Int, [SqlValue])])]
partByIter iC vs = pbi (zip [1..] vs)
    where
        pbi :: [(Int, [SqlValue])] -> [(Int, [(Int, [SqlValue])])]
        pbi ((p,v):vs) = let i = getIter v
                             (vi, vr) = span (\(p',v') -> i == getIter v') vs
                          in (i, (p, v):vi) : pbi vr
        pbi []         = []
        getIter :: [SqlValue] -> Int
        getIter vals = ((fromSql (vals !! iC))::Int)
        
type ResultInfo = (Int, Maybe (String, Int))

-- | Transform algebraic plan scheme info into resultinfo
schemeToResult :: P.Schema -> [(String, SqlColDesc)] -> ResultInfo
schemeToResult (itN, col) resDescr = let resColumns = flip zip [0..] $ map (\(c, _) -> takeWhile (\a -> a /= '_') c) resDescr
                                         itC = fromJust $ lookup itN resColumns
                                      in (itC, fmap (\(n, _) -> (n, fromJust $ lookup n resColumns)) col)
