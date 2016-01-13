{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Compare the result of DSH TPC-H queries on the validation dataset with the
-- expected result.
module Main where

import           System.Environment
import           System.Exit

import           Control.Monad

import qualified Test.Framework                 as F
import           Test.Framework.Providers.HUnit
import qualified Test.HUnit                     as H

import           Data.Decimal                   (Decimal)
import qualified Data.Text                      as T
import qualified Data.Time.Calendar             as C

import qualified Database.DSH                   as Q
import           Database.DSH.Backend
import           Database.DSH.Backend.Sql
import           Database.DSH.Compiler
import           Database.HDBC.ODBC

import           Queries.TPCH.Standard

eps :: Fractional a => a
eps = 0.01

stripWSSuffix :: T.Text -> T.Text
stripWSSuffix = T.dropWhileEnd (== ' ')

class RoughlyEq a where
    (~==) :: a -> a -> Bool

instance RoughlyEq T.Text where
    a ~== b = stripWSSuffix a == stripWSSuffix b

instance RoughlyEq Integer where
    (~==) = (==)

instance RoughlyEq Char where
    (~==) = (==)

instance RoughlyEq () where
    (~==) = (==)

instance RoughlyEq Double where
    a ~== b = abs (a - b) < eps

instance RoughlyEq Decimal where
    a ~== b = abs (a - b) < eps

instance RoughlyEq Q.Day where
    (~==) = (==)

instance RoughlyEq a => RoughlyEq [a] where
    as ~== bs = length as == length bs && and (zipWith (~==) as bs)

instance (RoughlyEq a, RoughlyEq b ,RoughlyEq c, RoughlyEq d, RoughlyEq e, RoughlyEq f, RoughlyEq g, RoughlyEq h) => RoughlyEq (a, b, c, d, e, f, g, h) where
    (a, b, c, d, e, f, g, h) ~== (a', b', c', d', e', f', g', h') = a ~== a' && b ~== b' && c ~== c' && d ~== d' && e ~== e' && f ~== f' && g ~== g' && h ~== h'

instance (RoughlyEq a, RoughlyEq b) => RoughlyEq (a, b) where
    (a, b) ~== (a', b') = a ~== a' && b ~== b'

instance (RoughlyEq a, RoughlyEq b, RoughlyEq c) => RoughlyEq (a, b, c) where
    (a, b, c) ~== (a', b', c') = a ~== a' && b ~== b' && c ~== c'

instance (RoughlyEq a, RoughlyEq b, RoughlyEq c, RoughlyEq d) => RoughlyEq (a, b, c, d) where
    (a, b, c, d) ~== (a', b', c', d') = a ~== a' && b ~== b' && c ~== c' && d ~== d'

makeEqAssertion :: (Show a, RoughlyEq a, Q.QA a, Backend c)
                => String
                -> Q.Q a
                -> a
                -> c
                -> H.Assertion
makeEqAssertion msg q expRes conn = do
    actualRes <- runQ conn q
    H.assertBool msg $ actualRes ~== expRes

makePredAssertion :: (Show a, RoughlyEq a, Q.QA a, Backend c)
                  => String
                  -> Q.Q a
                  -> [a -> Bool]
                  -> c
                  -> H.Assertion
makePredAssertion msg q preds conn = do
    actualRes <- runQ conn q
    H.assertBool msg $ all (\p -> p actualRes) preds

q1Test :: Backend c => c -> H.Assertion
q1Test = makeEqAssertion "q1" q1Default res
  where
    res = [ (("A", "F"), (37734107.0, 56586554400.73, 53758257134.8700, 55909065222.827692, 25.5220058532573370, 38273.129734621672, 0.04998529583839761162, 1478493))
          , (("N", "F"), (991417.00, 1487504710.38, 1413082168.0541, 1469649223.194375, 25.5164719205229835, 38284.467760848304, 0.05009342667421629691, 38854))
          , (("N", "O"), (74476040.00, 111701729697.74, 106118230307.6056, 110367043872.497010, 25.5022267695849915, 38249.117988908270, 0.04999658605370408037, 2920374))
          , (("R", "F"), (37719753.00, 56568041380.90, 53741292684.6040, 55889619119.831932, 25.5057936126907707, 38250.854626099657, 0.05000940583012705647, 1478870))
          ]

q2Test :: Backend c => c -> H.Assertion
q2Test = makePredAssertion "q2" q2Default [p1, p2]
  where
    p1 xs = take 4 xs  ~== r1
    p2 xs = drop (length xs - 4) xs ~== r2

    r1 = [ (9938.53, "Supplier#000005359","UNITED KINGDOM",185358,"Manufacturer#4","QKuHYh,vZGiwu2FWEJoLDx04","33-429-790-6131","uriously regular requests hag")
         , (9937.84, "Supplier#000005969","ROMANIA",108438,"Manufacturer#1","ANDENSOSmk,miq23Xfb5RWt6dvUcvt6Qa","29-520-692-3537","efully express instructions. regular requests against the slyly fin")
         , (9936.22, "Supplier#000005250","UNITED KINGDOM",249,"Manufacturer#4","B3rqp0xbSEim4Mpy2RH J","33-320-228-2957","etect about the furiously final accounts. slyly ironic pinto beans sleep inside the furiously")
         , (9923.77, "Supplier#000002324","GERMANY",29821,"Manufacturer#4","y3OD9UywSTOk","17-779-299-1839","ackages boost blithely. blithely regular deposits c")
         ]


    r2 = [ (7871.50,"Supplier#000007206","RUSSIA",104695,"Manufacturer#1","3w fNCnrVmvJjE95sgWZzvW","32-432-452-7731","ironic requests. furiously final theodolites cajole. final, express packages sleep. quickly reg")
         , (7852.45,"Supplier#000005864","RUSSIA",8363,"Manufacturer#4","WCNfBPZeSXh3h,c","32-454-883-3821","usly unusual pinto beans. brave ideas sleep carefully quickly ironi")
         , (7850.66,"Supplier#000001518","UNITED KINGDOM",86501,"Manufacturer#1","ONda3YJiHKJOC","33-730-383-3892","ifts haggle fluffily pending pai")
         , (7843.52,"Supplier#000006683","FRANCE",11680,"Manufacturer#4","2Z0JGkiv01Y00oCFwUGfviIbhzCdy","16-464-517-8943"," express, final pinto beans x-ray slyly asymptotes. unusual, unusual")
         ]

q3Test :: Backend c => c -> H.Assertion
q3Test = makeEqAssertion "q3" q3Default res
  where
    res = [ ((2456423, C.fromGregorian 1995 03 05, 0), 406181.0111)
          , ((3459808, C.fromGregorian 1995 03 04, 0), 405838.6989)
          , ((492164, C.fromGregorian 1995 02 19, 0), 390324.0610)
          , ((1188320, C.fromGregorian 1995 03 09, 0), 384537.9359)
          , ((2435712, C.fromGregorian 1995 02 26, 0), 378673.0558)
          , ((4878020, C.fromGregorian 1995 03 12, 0), 378376.7952)
          , ((5521732, C.fromGregorian 1995 03 13, 0), 375153.9215)
          , ((2628192, C.fromGregorian 1995 02 22, 0), 373133.3094)
          , ((993600, C.fromGregorian 1995 03 05, 0), 371407.4595)
          , ((2300070, C.fromGregorian 1995 03 13, 0), 367371.1452)
          ]

q15Test :: Backend c => c -> H.Assertion
q15Test = makeEqAssertion "q15" q15Default res
  where
    res = [ (8449, ("Supplier#000008449", "Wp34zim9qYFbVctdW", "20-469-856-8873", 1772627.2087))]

q21Test :: Backend c => c -> H.Assertion
q21Test = makePredAssertion "q21" q21Default [p1, p2, p3]
  where
    p1 xs = length xs == 100
    p2 xs = take 4 xs ~== r1
    p3 xs = drop (length xs - 4) xs ~== r2

    r1 = [ ("Supplier#000002829", 20)
         , ("Supplier#000005808", 18)
         , ("Supplier#000000262", 17)
         , ("Supplier#000000496", 17)
         ]

    r2 = [ ("Supplier#000001925", 12)
         , ("Supplier#000002039", 12)
         , ("Supplier#000002357", 12)
         , ("Supplier#000002483", 12)
         ]

tests :: Backend c => c -> [F.Test]
tests c =
    [ testCase "q1" (q1Test c)
    , testCase "q2" (q2Test c)
    , testCase "q3" (q3Test c)
    , testCase "q15" (q15Test c)
    , testCase "q21" (q21Test c)
    ]

main :: IO ()
main = do
    args <- getArgs
    when ("--help" `elem` args) $ do
        putStrLn "Usage: test-tpch [test-framework args] <dbname>"
        withArgs ["--help"] $ F.defaultMain []
        exitFailure
    let tfArgs = init args
        db     = last args
    conn <- sqlBackend <$> connectODBC ("DSN=" ++ db)
    withArgs tfArgs $ F.defaultMain (tests conn)
