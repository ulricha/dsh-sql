{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Translate DSH frontend expressions (implicitly typed through
-- GADT) into explicitly typed DSH backend expressions.
module Database.DSH.Translate.Frontend2CL (toComprehensions) where

import           Database.DSH.Impossible

import qualified Database.DSH.CL.Lang            as CL
import qualified Database.DSH.CL.Primitives      as CP
import qualified Database.DSH.Common.Lang        as L
import qualified Database.DSH.Common.Type        as T

import           Data.Text                       (unpack)
import           Database.DSH.Frontend.Funs
import           Database.DSH.Frontend.TupleTypes
import           Database.DSH.Frontend.Internals

import qualified Data.Map                        as M

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State

import           Text.Printf

import           GHC.Exts                        (sortWith)

-- | For each column, we need the name of the column, a string
-- description of the type for error messsages and a function to check
-- a DSH base type for compability with the column.
type TableInfo = [(String, String, (T.Type -> Bool))]

type TableInfoCache = M.Map String TableInfo

type QueryTableInfo = String -> IO TableInfo

-- In the state, we store a counter for fresh variable names, the
-- cache for table information and the backend-specific IO function
-- that retrieves not-yet-cached table information.
type CompileState = (Integer, TableInfoCache, QueryTableInfo)

-- | The Compile monad provides fresh variable names, allows to
-- retrieve information about tables from the database backend and
-- caches table information.
type Compile = StateT  CompileState IO

-- | Lookup information that describes a table. If the information is
-- not present in the state then the connection is used to retrieve
-- the table information from the Database.
tableInfo :: String -> Compile TableInfo
tableInfo tableName = do
    (i, env, f) <- get
    case M.lookup tableName env of
        Nothing -> do
            inf <- getTableInfoFun tableName
            put (i, M.insert tableName inf env, f)
            return inf
        Just v -> return v

-- | Provide a fresh identifier name during compilation
freshVar :: Compile Integer
freshVar = do
    (i, m, f) <- get
    put (i + 1, m, f)
    return i

prefixVar :: Integer -> String
prefixVar i = "v" ++ show i

getTableInfoFun :: String -> Compile TableInfo
getTableInfoFun tableName = do
    (_, _, queryTableInfo) <- get
    lift $ queryTableInfo tableName

-- | Translate a DSH frontend expression into the internal
-- comprehension-based language. 'queryTableInfo' abstracts asking a
-- database for information about tables, which might be performed
-- using one of the existing backends (X100, SQL).
toComprehensions :: QueryTableInfo -> Exp a -> IO CL.Expr
toComprehensions queryTableInfo e = runCompile queryTableInfo $ translate e

-- | Execute the transformation computation. During compilation table
-- information can be retrieved from the database, therefore the result
-- is wrapped in the IO Monad.
runCompile :: QueryTableInfo -> Compile a -> IO a
runCompile f = liftM fst . flip runStateT (1, M.empty, f)


translate :: forall a. Exp a -> Compile CL.Expr
translate (TupleConstE tc) = let translateTupleConst = $(mkTranslateTupleTerm 16)
                             in translateTupleConst tc
{-
    a' <- translate a 
    b' <- translate b
    c' <- translate c
    let elemTys = map T.typeOf [a', b', c']
    return $ CL.MkTuple (T.TupleT $ map T.typeOf [a', b', c']) [a', b', c']
-}
translate UnitE = return $ CP.unit
translate (BoolE b) = return $ CP.bool b
translate (CharE c) = return $ CP.string [c]
translate (IntegerE i) = return $ CP.int (fromInteger i)
translate (DoubleE d) = return $ CP.double d
translate (TextE t) = return $ CP.string (unpack t)
translate (PairE e1 e2) = CP.pair <$> translate e1 <*> translate e2
translate (VarE i) = do
    let ty = reify (undefined :: a)
    return $ CP.var (translateType ty) (prefixVar i)
translate (ListE es) = do
    let ty = reify (undefined :: a)
    CP.list (translateType ty) <$> mapM translate es
translate (e@(LamE _)) =
    case e of
        (LamE f :: Exp (b -> c)) -> do
            v <- freshVar
            let ty = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
            CP.lambda (translateType ty) (prefixVar v) <$> (translate $ f (VarE v :: Exp b))
        _ -> $impossible
translate (TableE (TableDB tableName hints)) = do
    -- Reify the type of the table expression
    let ty = reify (undefined :: a)

    -- Extract the column types from the frontend type
    let ts = tableTypes ty

    -- Fetch the actual type of the table from the database
    -- backend. Since we can't refer to columns by name from the
    -- Haskell side, we sort the columns by name to get a canonical
    -- order.
    tableDescr <- sortWith (\(n, _, _) -> n) <$> tableInfo tableName

    let tableTypeError = printf "DSH type and type of table %s are incompatible:\nDSH: %s\nDatabase: %s"
                                tableName
                                (show ts)
                                (show $ map (\(n, t, _) -> (n, t)) tableDescr)

    -- The DSH record/tuple type must match the number of columns in
    -- the database table
    if length tableDescr == length ts
        then return ()
        else error tableTypeError

    let matchTypes :: (String, String, T.Type -> Bool) -> T.Type -> (L.ColName, T.Type)
        matchTypes (colName, _, typesCompatible) dshType =
            if typesCompatible dshType
            then (L.ColName colName, dshType)
            else error tableTypeError

    let cols = zipWith matchTypes tableDescr ts

    return $ CP.table (translateType ty) tableName cols (compileHints hints)

translate (AppE f args) = compileApp f args

compileHints :: TableHints -> L.TableHints
compileHints hints = L.TableHints { L.keysHint = keys $ keysHint hints
                                  , L.nonEmptyHint = ne $ nonEmptyHint hints
                                  }
  where
    keys :: [Key] -> [L.Key]
    keys ks = [ L.Key [ L.ColName c | c <- k ] | Key k <- ks ]

    ne :: Emptiness -> L.Emptiness
    ne NonEmpty      = L.NonEmpty
    ne PossiblyEmpty = L.PossiblyEmpty


compileApp3 :: (CL.Expr -> CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, (b, c)) -> Compile CL.Expr
compileApp3 f (PairE e1 (PairE e2 e3)) = f <$> translate e1 <*> translate e2 <*> translate e3
compileApp3 _ _ = $impossible

compileApp2 :: (CL.Expr -> CL.Expr -> CL.Expr) -> Exp (a, b) -> Compile CL.Expr
compileApp2 f (PairE e1 e2) = f <$> translate e1 <*> translate e2
compileApp2 _ _ = $impossible

compileApp1 :: (CL.Expr -> CL.Expr) -> Exp a -> Compile CL.Expr
compileApp1 f e = f <$> translate e



-- | Translate DSH frontend types into backend types.
translateType :: Type a -> T.Type
translateType UnitT          = T.unitT
translateType BoolT          = T.boolT
translateType CharT          = T.stringT
translateType IntegerT       = T.intT
translateType DoubleT        = T.doubleT
translateType TextT          = T.stringT
translateType (PairT t1 t2)  = T.pairT (translateType t1) (translateType t2)
translateType (ListT t)      = T.listT (translateType t)
translateType (ArrowT t1 t2) = (translateType t1) T..-> (translateType t2)
translateType (TupleT (Tuple3T t1 t2 t3)) = T.TupleT [(translateType t1), translateType t2, translateType t3]

-- | From the type of a table (a list of base records represented as
-- right-deep nested tuples) extract the types of the individual
-- fields.

-- FIXME check more thoroughly that the type is actually of the shape
-- we expect.
tableTypes :: Type [a] -> [T.Type]
tableTypes (ListT t) = fromTuples t
  where
    fromTuples :: Type a -> [T.Type]
    fromTuples (PairT t1 t2) = translateType t1 : fromTuples t2
    fromTuples t'            = [translateType t']

compileApp :: Fun a b -> Exp a -> Compile CL.Expr
compileApp f args =
    case f of
       -- Builtin functions with arity three
       Cond -> compileApp3 CP.cond args

       -- Builtin functions with arity two
       Add          -> compileApp2 CP.add args
       Mul          -> compileApp2 CP.mul args
       Sub          -> compileApp2 CP.sub args
       Div          -> compileApp2 CP.div args
       Mod          -> compileApp2 CP.mod args
       Index        -> compileApp2 CP.index args
       SortWith     -> compileApp2 CP.sortWith args
       Cons         -> compileApp2 CP.consOpt args
       Map          -> compileApp2 CP.map args
       ConcatMap    -> compileApp2 CP.concatMap args
       Append       -> compileApp2 CP.append args
       Filter       -> compileApp2 CP.filter args
       GroupWithKey -> compileApp2 CP.groupWithKey args
       Zip          -> compileApp2 CP.zip args
       Equ          -> compileApp2 CP.eq args
       NEq          -> compileApp2 CP.neq args
       Conj         -> compileApp2 CP.conj args
       Disj         -> compileApp2 CP.disj args
       Lt           -> compileApp2 CP.lt args
       Lte          -> compileApp2 CP.lte args
       Gte          -> compileApp2 CP.gte args
       Gt           -> compileApp2 CP.gt args
       Like         -> compileApp2 CP.like args

       -- Builtin functions with arity one
       IntegerToDouble -> compileApp1 CP.castDouble args
       Not             -> compileApp1 CP.not args
       Sin             -> compileApp1 CP.sin args
       Cos             -> compileApp1 CP.cos args
       Tan             -> compileApp1 CP.tan args
       ASin            -> compileApp1 CP.asin args
       ACos            -> compileApp1 CP.acos args
       ATan            -> compileApp1 CP.atan args
       Sqrt            -> compileApp1 CP.sqrt args
       Log             -> compileApp1 CP.log args
       Exp             -> compileApp1 CP.exp args
       Fst             -> compileApp1 CP.fst args
       Snd             -> compileApp1 CP.snd args
       Head            -> compileApp1 CP.head args
       Tail            -> compileApp1 CP.tail args
       Minimum         -> compileApp1 CP.minimum args
       Maximum         -> compileApp1 CP.maximum args
       Concat          -> compileApp1 CP.concat args
       Sum             -> compileApp1 CP.sum args
       Avg             -> compileApp1 CP.avg args
       And             -> compileApp1 CP.and args
       Or              -> compileApp1 CP.or args
       Reverse         -> compileApp1 CP.reverse args
       Number          -> compileApp1 CP.number args
       Length          -> compileApp1 CP.length args
       Null            -> compileApp1 CP.null args
       Init            -> compileApp1 CP.init args
       Last            -> compileApp1 CP.last args
       Nub             -> compileApp1 CP.nub args
       Guard           -> compileApp1 CP.guard args
       Transpose       -> compileApp1 CP.transpose args
       Reshape n       -> compileApp1 (CP.reshape n) args
       TupElem te      -> let compileTupElem = $(mkTupElemCompile 5)
                          in compileTupElem te args
