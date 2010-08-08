{-# LANGUAGE TemplateHaskell, RankNTypes, RelaxedPolyRec #-}
{-# OPTIONS -fno-warn-orphans #-}

module Ferry.TH
    (
      deriveTupleQA
    , generateDeriveTupleQARange
    , deriveTupleTA
    , generateDeriveTupleTARange
    , deriveTupleView
    , generateDeriveTupleViewRange

    , deriveQAForRecord
    , deriveQAForRecord'
    , deriveViewForRecord
    , deriveViewForRecord'
    , deriveTAForRecord
    , deriveTAForRecord'
    , deriveRecordInstances
    , createTableRepresentation
    ) where

import Control.Applicative
import Control.Monad
import Data.Convertible
import Data.List
import Database.HDBC

import Ferry.Data
import Ferry.Class
import Ferry.Impossible
import Language.Haskell.TH hiding (Q, TupleT, tupleT, AppE, VarE, reify, Type, ListT)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (sequenceQ)


-- Create a "a -> b -> ..." type
arrowChainT :: [TypeQ] -> TypeQ
arrowChainT [] = $impossible
arrowChainT as = foldr1 (\a b -> arrowT `appT` a `appT` b) as

-- Apply a list of 'TypeQ's to a type constructor
applyChainT :: TypeQ -> [TypeQ] -> TypeQ
applyChainT t ts = foldl' appT t ts

-- Apply a list of 'Exp's to a some 'Exp'
applyChainE :: ExpQ -> [ExpQ] -> ExpQ
applyChainE e es = foldl' appE e es


-- Some Applicative magic :)
instance Applicative TH.Q where
    pure  = return
    (<*>) = ap

--
-- * QA instances
--

deriveTupleQA :: Int -> TH.Q [Dec]
deriveTupleQA l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD qaCxts
                                        qaType
                                        qaDecs

  where
    names@(a:b:rest) = [ mkName $ "a" ++ show i | i <- [1..l] ]

    qaCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    qaType = conT ''QA `appT` applyChainT (TH.tupleT l) (map varT names)
    qaDecs = [ reifyDec
             , fromNormDec
             , toNormDec
             ]

    -- The class functions:

    reifyDec    = funD 'reify [reifyClause]
    reifyClause = clause [ wildP ]
                         ( normalB [| foldr1 TupleT $(listE [ [| reify (undefined :: $_n) |]
                                                            | _n <- map varT names
                                                            ] )
                                    |] )
                         [ ]

    fromNormDec    = funD 'fromNorm [fromNormClause]
    fromNormClause = clause [foldr1 (\p1 p2 -> conP 'TupleN [p1,p2]) (map varP names)]
                            (normalB $ TH.tupE [ [| fromNorm $(varE n) |] | n <- names ])
                            []

    toNormDec    = funD 'toNorm [toNormClause]
    toNormClause = clause [ tupP [ varP n | n <- names ] ]
                          ( normalB [|  (foldr1 TupleN $(listE [ [|toNorm $(varE n) |] | n <- names ]))
                                    |] )
                          []

-- | Generate all 'QA' instances for tuples within range.
generateDeriveTupleQARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleQARange from to =
    concat `fmap` sequenceQ [ deriveTupleQA n | n <- reverse [from..to] ]


--
-- * TA instances
--

-- Original code:
-- instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

deriveTupleTA :: Int -> TH.Q [Dec]
deriveTupleTA l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD taCxts
                                        taType
                                        taDecs

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]

    taCxts = return $ concat [ [ClassP ''QA [VarT n], ClassP ''BasicType [VarT n]] | n <- names ]
    taType = conT ''TA `appT` applyChainT (TH.tupleT l) (map varT names)
    taDecs = []

-- | Generate all 'TA' instances for tuples within range.
generateDeriveTupleTARange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleTARange from to =
    concat `fmap` sequenceQ [ deriveTupleTA n | n <- reverse [from..to] ]


--
-- * View pattern
--


-- Original code:
-- instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
--   view (Q a) = (Q (AppE (VarE "proj_2_1") a), Q (AppE (VarE "proj_2_1") a))

deriveTupleView :: Int -> TH.Q [Dec]
deriveTupleView l
    | l < 2     = $impossible
    | otherwise = pure `fmap` instanceD viewCxts
                                        viewType
                                        viewDecs

  where
    names = [ mkName $ "a" ++ show i | i <- [1..l] ]
    a = mkName "a"

    first  p = [| AppE (VarE "fst") $p |]
    second p = [| AppE (VarE "snd") $p |]

    viewCxts = return [ ClassP ''QA [VarT n] | n <- names ]
    viewType = conT ''View `appT` (conT ''Q `appT` applyChainT (TH.tupleT l) (map varT names))
                           `appT` applyChainT (TH.tupleT l) [ conT ''Q `appT` varT n | n <- names ]

    viewDecs = [ viewDec, fromViewDec ]

    viewDec    = funD 'view [viewClause]
    viewClause = clause [ conP 'Q [varP a] ]
                        ( normalB $ TH.tupE [ if pos == l then [| Q $(f (varE a)) |] else [| Q $(first (f (varE a))) |]
                                            | pos <- [1..l]
                                            , let f = foldr (.) id (replicate (pos - 1) second)
                                            ])
                        []

    fromViewDec = funD 'fromView [fromViewClause]
    fromViewClause = clause [ tupP (map (\n -> conP 'Q [varP n]) names) ]
                            ( normalB [| Q  $(foldr1 (\e1 e2 -> appE (appE (conE 'TupleE) e1) e2) (map varE names)) |] )
                            []

-- | Generate all 'View' instances for tuples within range.
generateDeriveTupleViewRange :: Int -> Int -> TH.Q [Dec]
generateDeriveTupleViewRange from to =
    concat `fmap` sequenceQ [ deriveTupleView n | n <- reverse [from..to] ]




--------------------------------------------------------------------------------
-- * Deriving Instances for Records
--

-- | Derive the 'QA' instance for a record definition.
deriveQAForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveQAForRecord q = (++) <$> q
                           <*> deriveQAForRecord' q

-- | Add 'QA' instance to a record without adding the actual data definition.
-- Usefull in combination with 'deriveQAForRecord''
deriveQAForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveQAForRecord' q = do
    d <- q
    mapM addInst d
  where
    addInst d@(DataD [] dName [] [RecC rName rVar@(_:_)] _) | dName == rName = do

         let rCxt  = return []
             rType = conT ''QA `appT` conT dName
             rDec  = [ reifyDec
                     , toNormDec
                     , fromNormDec
                     ]

             reifyDec    = funD 'reify [reifyClause]
             reifyClause = clause [ recP rName [] ]
                                  ( normalB $ [| foldr1 TupleT $(listE [ [| reify (undefined :: $(return _t)) |]
                                                                       | (_,_,_t) <- rVar
                                                                       ])
                                              |])
                                  []

             names = [ mkName $ "a" ++ show i | i <- [1..length rVar] ]

             fromNormDec    = funD 'fromNorm [fromNormClause, failClause]
             fromNormClause = clause [ foldr1 (\p1 p2 -> conP 'TupleN [p1,p2]) (map varP names) ]
                                     ( normalB $ (conE dName) `applyChainE` [ [| fromNorm $(varE n) |]
                                                                            | n <- names
                                                                            ]
                                     )
                                     []

             -- Fail with a verbose message where this happened
             failClause = clause [ wildP ]
                                 ( do loc <- location
                                      let pos = show (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
                                      normalB [| error $ "ferry: Impossible `fromNorm' at location " ++ pos |]
                                 )
                                 []

             toNormDec    = funD 'toNorm [toNormClause]
             toNormClause = clause [ conP dName (map varP names) ]
                                   ( normalB [| foldr1 TupleN $(listE [ [| toNorm $(varE n) |]
                                                                      | n <- names ])
                                             |] )
                                   []

         instanceD rCxt
                   rType
                   rDec

    addInst _ = error "ferry: Failed to derive 'QA' - Invalid record definition"

-- | Derive the 'View' instance for a record definition. See
-- 'deriveQAForRecord' for an example.
deriveViewForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveViewForRecord q = (++) <$> q
                             <*> deriveViewForRecord' q

-- | Add 'View' instance to a record without adding the actual data definition.
-- Usefull in combination with 'deriveQAForRecord''
deriveViewForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveViewForRecord' q = do
    d <- q
    concat `fmap` mapM addView d
  where
    addView (DataD [] dName [] [RecC rName rVar@(_:_)] dNames) | dName == rName = do

        -- The "View" record definition

        let vName  = mkName $ nameBase dName ++ "V"
            vRec   = recC vName [ return (prefixV n, s, makeQ t) | (n,s,t) <- rVar ]

            prefixV :: Name -> Name
            prefixV n = mkName $ "v_" ++ nameBase n

            makeQ :: TH.Type -> TH.Type
            makeQ t = ConT ''Q `AppT` t

            vNames = dNames

        v <- dataD (return [])
                   vName
                   []
                   [vRec]
                   vNames

        -- The instance definition

        let rCxt  = return []
            rType = conT ''View `appT` (conT ''Q `appT` conT dName)
                                `appT` (conT vName)
            rDec  = [ viewDec
                    , fromViewDec
                    ]

            a = mkName "a"

            viewDec    = funD 'view [viewClause]
            viewClause = clause [ conP 'Q [varP a] ]
                                ( normalB $ applyChainE (conE vName)
                                                        [ [| Q (AppE (VarE n) $(varE a)) |]
                                                        | n <- map (\(n,_,_) -> nameBase n) rVar
                                                        ]
                                )
                                []

            -- names for variables used in the `fromView' function
            fvNames@(_:qs) = [ mkName $ "q" ++ show i | i <- [1.. length rVar] ]

            fromViewDec    = funD 'fromView [fromViewClause, failClause]
            fromViewClause = clause [ conP vName $  (conP 'Q [conP 'AppE [wildP, varP a]]) : [ wildP | _ <- qs ] ]
                                    ( normalB [| Q $(varE a) |] )
                                    []

            -- Fail with a verbose message where this happened
            failClause = clause [ wildP ]
                                ( do loc <- location
                                     let pos = show (TH.loc_filename loc, fst (TH.loc_start loc), snd (TH.loc_start loc))
                                     normalB [| error $ "ferry: Impossible `fromView' at location " ++ pos |]
                                )
                                []

        i <- instanceD rCxt
                       rType
                       rDec

        return [v,i]

    addView _ = error "ferry: Failed to derive 'View' - Invalid record definition"


-- | Derive 'TA' instances
deriveTAForRecord :: TH.Q [Dec] -> TH.Q [Dec]
deriveTAForRecord q = (++) <$> q
                           <*> deriveTAForRecord' q

deriveTAForRecord' :: TH.Q [Dec] -> TH.Q [Dec]
deriveTAForRecord' q = do
    d <- q
    mapM addTA d
  where
    addTA (DataD [] dName [] [RecC rName (_:_)] _) | dName == rName =

        let taCxt  = return []
            taType = conT ''TA `appT` conT dName
            taDec  = [ ]

        in instanceD taCxt
                     taType
                     taDec

    addTA _ = error "ferry: Failed to derive 'TA' - Invalid record definition"


-- | Derive all necessary instances for record definitions
--
-- Example usage:
--
-- > $(deriveRecordInstances [d|
-- >
-- >     data User = User
-- >         { user_id    :: Int
-- >         , user_name  :: String
-- >         }
-- >
-- >   |])
deriveRecordInstances :: TH.Q [Dec] -> TH.Q [Dec]
deriveRecordInstances q = do
    d  <- q
    qa <- deriveQAForRecord' q
    v  <- deriveViewForRecord' q
    ta <- deriveTAForRecord' q
    return $ d ++ qa ++ v ++ ta


-- | Lookup a table and create its data type representation
--
-- Example usage:
--
-- > $(createTableRepresentation myConnection "t_user" "User" [''Show, ''Eq])
--
-- Note that this representation is created on compile time, not on run time!
createTableRepresentation :: (IConnection conn)
                          => (IO conn)  -- ^ Database connection
                          -> String     -- ^ Table name
                          -> String     -- ^ Data type name for each row of the table
                          -> [Name]     -- ^ Default deriving instances
                          -> TH.Q [Dec]
createTableRepresentation conn t dname dnames = do
    tdesc <- runIO $ do
        c <- conn
        describeTable c t
    deriveRecordInstances $ createDataType tdesc

  where
    createDataType :: [(String, SqlColDesc)] -> TH.Q [Dec]
    createDataType [] = error "ferry: Empty table description"
    createDataType ds = pure `fmap` dataD dCxt
                                          dName
                                          []
                                          [dCon ds]
                                          dNames

    dName     = mkName dname
    dNames    = dnames

    dCxt      = return []
    dCon desc = recC dName (map toVarStrictType desc)

    -- no support for nullable columns yet:
    toVarStrictType (n,SqlColDesc { colType = ty, colNullable = _ }) =
        let t' = case convert ty of
                      IntT        -> ConT ''Int
                      BoolT       -> ConT ''Bool
                      CharT       -> ConT ''Char
                      ListT CharT -> ConT ''String
                      _           -> $impossible

        in return (mkName n, NotStrict, t')
