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

q4Test :: Backend c => c -> H.Assertion
q4Test = makeEqAssertion "q4" q4Default res
  where
    res = [ ("1-URGENT", 10594)
          , ("2-HIGH", 10476)
          , ("3-MEDIUM", 10410)
          , ("4-NOT SPECIFIED", 10556)
          , ("5-LOW", 10487)
          ]

q5Test :: Backend c => c -> H.Assertion
q5Test = makeEqAssertion "q5" q5Default res
  where
    res = [ ("INDONESIA", 55502041.1697)
          , ("VIETNAM", 55295086.9967)
          , ("CHINA", 53724494.2566)
          , ("INDIA", 52035512.0002)
          , ("JAPAN", 45410175.69540)
          ]

q6Test :: Backend c => c -> H.Assertion
q6Test = makeEqAssertion "q6" q6Default res
  where
    res = 123141078.23

q7Test :: Backend c => c -> H.Assertion
q7Test = makeEqAssertion "q7" q7Default res
  where
    res = [ (("FRANCE", "GERMANY", 1995), 54639732.7336)
          , (("FRANCE", "GERMANY", 1996), 54633083.3076)
          , (("GERMANY", "FRANCE", 1995), 52531746.6697)
          , (("GERMANY", "FRANCE", 1996), 52520549.0224) ]

q8Test :: Backend c => c -> H.Assertion
q8Test = makeEqAssertion "q8" q8Default res
  where
    res = [(1995, 0.03443589040665479743), (1996, 0.04148552129353032075)]

q10Test :: Backend c => c -> H.Assertion
q10Test = makeEqAssertion "q10" q10Default res
  where
    res = [ (57040, "Customer#000057040", 734235.2455, 632.87,  "JAPAN", "Eioyzjf4pp", "22-895-641-3466", "sits. slyly regular requests sleep alongside of the regular inst")
          , (143347, "Customer#000143347", 721002.6948, 2557.47, "EGYPT", "1aReFYv,Kw4", "14-742-935-3718", "ggle carefully enticing requests. final deposits use bold, bold pinto beans. ironic, idle re")
          , (60838, "Customer#000060838", 679127.3077, 2454.77, "BRAZIL", "64EaJ5vMAHWJlBOxJklpNc2RJiWE", "12-913-494-9813", "need to boost against the slyly regular account")
          , (101998, "Customer#000101998", 637029.5667, 3790.89, "UNITED KINGDOM", "01c9CILnNtfOQYmZj", "33-593-865-6378", "ress foxes wake slyly after the bold excuses. ironic platelets are furiously carefully bold theodolites")
          , (125341, "Customer#000125341", 633508.0860, 4983.51, "GERMANY", "S29ODD6bceU8QSuuEJznkNaK", "17-582-695-5962", "arefully even depths. blithely even excuses sleep furiously. foxes use except the dependencies. ca")
          , (25501, "Customer#000025501", 620269.7849, 7725.04, "ETHIOPIA", "W556MXuoiaYCCZamJI,Rn0B4ACUGdkQ8DZ", "15-874-808-6793", "he pending instructions wake carefully at the pinto beans. regular, final instructions along the slyly fina")
          , (115831, "Customer#000115831", 596423.8672, 5098.10, "FRANCE", "rFeBbEEyk dl ne7zVq1oK09wV7pxqCgIc", "16-715-386-3788", "l somas sleep. furiously final deposits wake blithely regular pinto b")
          , (84223, "Customer#000084223", 594998.0239, 528.65, "UNITED KINGDOM", "nAVZCs6BaWap rrM27N 2qBnzc5WBauxbA", "33-442-824-8191", "slyly final deposits haggle regular, pending dependencies. pending escapades wake")
          , (54289, "Customer#000054289", 585603.3918, 5583.02, "IRAN", "vXCxoCsU0Bad5JQI ,oobkZ", "20-834-292-4707", "ely special foxes are quickly finally ironic p")
          , (39922, "Customer#000039922", 584878.1134, 7321.11, "GERMANY", "Zgy4s50l2GKN4pLDPBU8m342gIw6R", "17-147-757-8036", "y final requests. furiously final foxes cajole blithely special platelets. f")
          , (6226, "Customer#000006226", 576783.7606, 2230.09, "UNITED KINGDOM", "8gPu8,NPGkfyQQ0hcIYUGPIBWc,ybP5g,", "33-657-701-3391", "ending platelets along the express deposits cajole carefully final")
          , (922, "Customer#000000922", 576767.5333, 3869.25, "GERMANY", "Az9RFaut7NkPnc5zSD2PwHgVwr4jRzq", "17-945-916-9648", "luffily fluffy deposits. packages c")
          , (147946, "Customer#000147946", 576455.1320, 2030.13, "ALGERIA", "iANyZHjqhyy7Ajah0pTrYyhJ", "10-886-956-3143", "ithely ironic deposits haggle blithely ironic requests. quickly regu")
          , (115640, "Customer#000115640", 569341.1933, 6436.10, "ARGENTINA", "Vtgfia9qI 7EpHgecU1X", "11-411-543-4901", "ost slyly along the patterns; pinto be")
          , (73606, "Customer#000073606", 568656.8578, 1785.67, "JAPAN", "xuR0Tro5yChDfOCrjkd2ol", "22-437-653-6966", "he furiously regular ideas. slowly")
          , (110246, "Customer#000110246", 566842.9815, 7763.35, "VIETNAM", "7KzflgX MDOq7sOkI", "31-943-426-9837", "egular deposits serve blithely above the fl")
          , (142549, "Customer#000142549", 563537.2368, 5085.99, "INDONESIA", "ChqEoK43OysjdHbtKCp6dKqjNyvvi9", "19-955-562-2398", "sleep pending courts. ironic deposits against the carefully unusual platelets cajole carefully express accounts.")
          , (146149, "Customer#000146149", 557254.9865, 1791.55, "ROMANIA", "s87fvzFQpU", "29-744-164-6487", "of the slyly silent accounts. quickly final accounts across the")
          , (52528, "Customer#000052528", 556397.3509, 551.79, "ARGENTINA", "NFztyTOR10UOJ", "11-208-192-3205", "deposits hinder. blithely pending asymptotes breach slyly regular re")
          , (23431, "Customer#000023431", 554269.5360, 3381.86, "ROMANIA", "HgiV0phqhaIa9aydNoIlb", "29-915-458-2654", "nusual, even instructions: furiously stealthy nm")]

q11Test :: Backend c => c -> H.Assertion
q11Test = makePredAssertion "q11" q11Default [p1, p2, p3]
  where
    p1 xs = length xs == 1048
    p2 xs = take 10 xs ~== r1
    p2 xs = drop (length xs - 4) ~== r2

    r1 = [ (129760, 17538456.86)
         , (166726, 16503353.92)
         , (191287, 16474801.97)
         , (161758, 16101755.54)
         , (34452, 15983844.72)
         , (139035, 15907078.34)
         , (9403, 15451755.62)
         , (154358, 15212937.88)
         , ( 38823, 15064802.86)
         , ( 85606, 15053957.15) ]

    r2 = [ (101674, 7879324.60)
         , (51968, 7879102.21)
         , (72073, 7877736.11)
         , (5182, 7874521.73) ]

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
    , testCase "q4" (q4Test c)
    , testCase "q5" (q5Test c)
    , testCase "q6" (q5Test c)
    , testCase "q15" (q15Test c)
    -- test disabled: PostgreSQL currently (13-01-16) generates a really bad
    -- plan and the query does not run in acceptable time.
    -- , testCase "q21" (q21Test c)
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
