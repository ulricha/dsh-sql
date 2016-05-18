{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Compare the result of DSH TPC-H queries on the validation dataset with the
-- expected result.
module Main where

import           Debug.Trace

import           System.Environment
import           System.Exit

import           Control.Monad

import qualified Test.HUnit               as H
import           Test.Tasty
import qualified Test.Tasty.HUnit         as TH

import           Data.Decimal             (Decimal)
import qualified Data.Text                as T
import qualified Data.Time.Calendar       as C

import qualified Database.DSH             as Q
import           Database.DSH.Backend
import           Database.DSH.Backend.Sql
import           Database.DSH.Compiler
import           Database.HDBC.ODBC

import           Queries.TPCH.Standard

eps :: Fractional a => a
eps = 0.01

stripWSSuffix :: T.Text -> T.Text
stripWSSuffix = T.dropWhileEnd (== ' ')


(~===) :: (RoughlyEq a, Show a) => a -> a -> Bool
a ~=== b | a ~== b    = True
        | otherwise = trace (show a ++ " /= " ++ show b) False

class Eq a => RoughlyEq a where
    (~==) :: a -> a -> Bool
    (~==) = (==)

instance RoughlyEq T.Text where
    a ~== b = stripWSSuffix a == stripWSSuffix b

instance RoughlyEq Integer where

instance RoughlyEq Char where

instance RoughlyEq () where

instance RoughlyEq Double where
    a ~== b = abs (a - b) < eps

instance RoughlyEq Decimal where
    a ~== b = abs (a - b) < eps

instance RoughlyEq Q.Day where

instance (RoughlyEq a, Show a) => RoughlyEq [a] where
    as ~== bs = length as == length bs && and (zipWith (~===) as bs)

instance (RoughlyEq a, RoughlyEq b ,RoughlyEq c, RoughlyEq d, RoughlyEq e, RoughlyEq f, RoughlyEq g, RoughlyEq h) => RoughlyEq (a, b, c, d, e, f, g, h) where
    (a, b, c, d, e, f, g, h) ~== (a', b', c', d', e', f', g', h') = a ~== a' && b ~== b' && c ~== c' && d ~== d' && e ~== e' && f ~== f' && g ~== g' && h ~== h'

instance (RoughlyEq a, RoughlyEq b) => RoughlyEq (a, b) where
    (a, b) ~== (a', b') = a ~== a' && b ~== b'

instance (RoughlyEq a, RoughlyEq b, RoughlyEq c) => RoughlyEq (a, b, c) where
    (a, b, c) ~== (a', b', c') = a ~== a' && b ~== b' && c ~== c'

instance (RoughlyEq a, RoughlyEq b, RoughlyEq c, RoughlyEq d) => RoughlyEq (a, b, c, d) where
    (a, b, c, d) ~== (a', b', c', d') = a ~== a' && b ~== b' && c ~== c' && d ~== d'

instance (RoughlyEq a, RoughlyEq b, RoughlyEq c, RoughlyEq d, RoughlyEq e) => RoughlyEq (a, b, c, d, e) where
    (a, b, c, d, e) ~== (a', b', c', d', e') = a ~== a' && b ~== b' && c ~== c' && d ~== d' && e ~== e'

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
    p1 xs = take 4 xs ~== r1
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

q9Test :: Backend c => c -> H.Assertion
q9Test = makePredAssertion "q9" q9Default [p1, p2, p3]
  where
    p1 xs = length xs == 175
    p2 xs = take 19 xs ~== r1
    p3 xs = drop (length xs - 11) xs ~== r2

    r1 = [ ("ALGERIA", 1998, 27136900.1803)
         , ("ALGERIA", 1997, 48611833.4962)
         , ("ALGERIA", 1996, 48285482.6782)
         , ("ALGERIA", 1995, 44402273.5999)
         , ("ALGERIA", 1994, 48694008.0668)
         , ("ALGERIA", 1993, 46044207.7838)
         , ("ALGERIA", 1992, 45636849.4881)
         , ("ARGENTINA", 1998, 28341663.7848)
         , ("ARGENTINA", 1997, 47143964.1176)
         , ("ARGENTINA", 1996, 45255278.6021)
         , ("ARGENTINA", 1995, 45631769.2054)
         , ("ARGENTINA", 1994, 48268856.3547)
         , ("ARGENTINA", 1993, 48605593.6162)
         , ("ARGENTINA", 1992, 46654240.7487)
         , ("BRAZIL", 1998, 26527736.3960)
         , ("BRAZIL", 1997, 45640660.7677)
         , ("BRAZIL", 1996, 45090647.1630)
         , ("BRAZIL", 1995, 44015888.5132)
         , ("BRAZIL", 1994, 44854218.8932) ]

    r2 = [ ("UNITED STATES", 1995, 48951591.6156)
         , ("UNITED STATES", 1994, 45099092.0598)
         , ("UNITED STATES", 1993, 46181600.5278)
         , ("UNITED STATES", 1992, 46168214.0901)
         , ("VIETNAM", 1998, 27281931.0011)
         , ("VIETNAM", 1997, 48735914.1796)
         , ("VIETNAM", 1996, 47824595.9040)
         , ("VIETNAM", 1995, 48235135.8016)
         , ("VIETNAM", 1994, 47729256.3324)
         , ("VIETNAM", 1993, 45352676.8672)
         , ("VIETNAM", 1992, 47846355.6485) ]

q10Test :: Backend c => c -> H.Assertion
q10Test = makeEqAssertion "q10" q10Default res
  where
    res = [ (57040, "Customer#000057040", 734235.2455, 632.87,  "JAPAN", "Eioyzjf4pp", "22-895-641-3466", "sits. slyly regular requests sleep alongside of the regular inst")
          , (143347, "Customer#000143347", 721002.6948, 2557.47, "EGYPT", "1aReFYv,Kw4", "14-742-935-3718", "ggle carefully enticing requests. final deposits use bold, bold pinto beans. ironic, idle re")
          , (60838, "Customer#000060838", 679127.3077, 2454.77, "BRAZIL", "64EaJ5vMAHWJlBOxJklpNc2RJiWE", "12-913-494-9813", " need to boost against the slyly regular account")
          , (101998, "Customer#000101998", 637029.5667, 3790.89, "UNITED KINGDOM", "01c9CILnNtfOQYmZj", "33-593-865-6378", "ress foxes wake slyly after the bold excuses. ironic platelets are furiously carefully bold theodolites")
          , (125341, "Customer#000125341", 633508.0860, 4983.51, "GERMANY", "S29ODD6bceU8QSuuEJznkNaK", "17-582-695-5962", "arefully even depths. blithely even excuses sleep furiously. foxes use except the dependencies. ca")
          , (25501, "Customer#000025501", 620269.7849, 7725.04, "ETHIOPIA", "  W556MXuoiaYCCZamJI,Rn0B4ACUGdkQ8DZ", "15-874-808-6793", "he pending instructions wake carefully at the pinto beans. regular, final instructions along the slyly fina")
          , (115831, "Customer#000115831", 596423.8672, 5098.10, "FRANCE", "rFeBbEEyk dl ne7zV5fDrmiq1oK09wV7pxqCgIc", "16-715-386-3788", "l somas sleep. furiously final deposits wake blithely regular pinto b")
          , (84223, "Customer#000084223", 594998.0239, 528.65, "UNITED KINGDOM", "nAVZCs6BaWap rrM27N 2qBnzc5WBauxbA", "33-442-824-8191", " slyly final deposits haggle regular, pending dependencies. pending escapades wake")
          , (54289, "Customer#000054289", 585603.3918, 5583.02, "IRAN", "vXCxoCsU0Bad5JQI ,oobkZ", "20-834-292-4707", "ely special foxes are quickly finally ironic p")
          , (39922, "Customer#000039922", 584878.1134, 7321.11, "GERMANY", "Zgy4s50l2GKN4pLDPBU8m342gIw6R", "17-147-757-8036", "y final requests. furiously final foxes cajole blithely special platelets. f")
          , (6226, "Customer#000006226", 576783.7606, 2230.09, "UNITED KINGDOM", "8gPu8,NPGkfyQQ0hcIYUGPIBWc,ybP5g,", "33-657-701-3391", "ending platelets along the express deposits cajole carefully final")
          , (922, "Customer#000000922", 576767.5333, 3869.25, "GERMANY", "Az9RFaut7NkPnc5zSD2PwHgVwr4jRzq", "17-945-916-9648", "luffily fluffy deposits. packages c")
          , (147946, "Customer#000147946", 576455.1320, 2030.13, "ALGERIA", "iANyZHjqhyy7Ajah0pTrYyhJ", "10-886-956-3143", "ithely ironic deposits haggle blithely ironic requests. quickly regu")
          , (115640, "Customer#000115640", 569341.1933, 6436.10, "ARGENTINA", "Vtgfia9qI 7EpHgecU1X", "11-411-543-4901", "ost slyly along the patterns; pinto be")
          , (73606, "Customer#000073606", 568656.8578, 1785.67, "JAPAN", "xuR0Tro5yChDfOCrjkd2ol", "22-437-653-6966", "he furiously regular ideas. slowly")
          , (110246, "Customer#000110246", 566842.9815, 7763.35, "VIETNAM", "7KzflgX MDOq7sOkI", "31-943-426-9837", "egular deposits serve blithely above the fl")
          , (142549, "Customer#000142549", 563537.2368, 5085.99, "INDONESIA", "ChqEoK43OysjdHbtKCp6dKqjNyvvi9", "19-955-562-2398", "sleep pending courts. ironic deposits against the carefully unusual platelets cajole carefully express accounts.")
          , (146149, "Customer#000146149", 557254.9865, 1791.55, "ROMANIA", "s87fvzFQpU", "29-744-164-6487", " of the slyly silent accounts. quickly final accounts across the ")
          , (52528, "Customer#000052528", 556397.3509, 551.79, "ARGENTINA", "NFztyTOR10UOJ", "11-208-192-3205", " deposits hinder. blithely pending asymptotes breach slyly regular re")
          , (23431, "Customer#000023431", 554269.5360, 3381.86, "ROMANIA", "HgiV0phqhaIa9aydNoIlb", "29-915-458-2654", "nusual, even instructions: furiously stealthy n")]

q11Test :: Backend c => c -> H.Assertion
q11Test = makePredAssertion "q11" q11Default [p1, p2, p3]
  where
    p1 xs = length xs == 1048
    p2 xs = take 10 xs ~== r1
    p3 xs = drop (length xs - 4) xs ~== r2

    r1 = [ (129760, 17538456.86)
         , (166726, 16503353.92)
         , (191287, 16474801.97)
         , (161758, 16101755.54)
         , (34452, 15983844.72)
         , (139035, 15907078.34)
         , (9403, 15451755.62)
         , (154358, 15212937.88)
         , (38823, 15064802.86)
         , (85606, 15053957.15) ]

    r2 = [ (101674, 7879324.60)
         , (51968, 7879102.21)
         , (72073, 7877736.11)
         , (5182, 7874521.73) ]

q12Test :: Backend c => c -> H.Assertion
q12Test = makeEqAssertion "q12" q12Default res
  where
    res = [ ("MAIL", 6202, 9324)
          , ("SHIP", 6200, 9262) ]

q13Test :: Backend c => c -> H.Assertion
q13Test = makeEqAssertion "q13" q13Default res
  where
    res = [ (0, 50005)
          , (9, 6641)
          , (10, 6532)
          , (11, 6014)
          , (8, 5937)
          , (12, 5639)
          , (13, 5024)
          , (19, 4793)
          , (7, 4687)
          , (17, 4587)
          , (18, 4529)
          , (20, 4516)
          , (15, 4505)
          , (14, 4446)
          , (16, 4273)
          , (21, 4190)
          , (22, 3623)
          , (6, 3265)
          , (23, 3225)
          , (24, 2742)
          , (25, 2086)
          , (5, 1948)
          , (26, 1612)
          , (27, 1179)
          , (4, 1007)
          , (28, 893)
          , (29, 593)
          , (3, 415)
          , (30, 376)
          , (31, 226)
          , (32, 148)
          , (2, 134)
          , (33, 75)
          , (34, 50)
          , (35, 37)
          , (1, 17)
          , (36, 14)
          , (38, 5)
          , (37, 5)
          , (40, 4)
          , (41, 2)
          , (39, 1) ]

q14Test :: Backend c => c -> H.Assertion
q14Test = makeEqAssertion "q14" q14Default res
  where
    res = 16.3807786263955401

q15Test :: Backend c => c -> H.Assertion
q15Test = makeEqAssertion "q15" q15Default res
  where
    res = [ (8449, ("Supplier#000008449", "Wp34zim9qYFbVctdW", "20-469-856-8873", 1772627.2087))]

q16Test :: Backend c => c -> H.Assertion
q16Test = makePredAssertion "q16" q16Default [p1, p2, p3]
  where
    p1 xs = length xs == 18314
    p2 xs = take 12 xs ~== r1
    p3 xs = drop (length xs - 15) xs ~== r2

    r1 = [ (("Brand#41", "MEDIUM BRUSHED TIN", 3), 28)
         , (("Brand#54", "STANDARD BRUSHED COPPER", 14), 27)
         , (("Brand#11", "STANDARD BRUSHED TIN", 23), 24)
         , (("Brand#11", "STANDARD BURNISHED BRASS", 36), 24)
         , (("Brand#15", "MEDIUM ANODIZED NICKEL", 3), 24)
         , (("Brand#15", "SMALL ANODIZED BRASS", 45), 24)
         , (("Brand#15", "SMALL BURNISHED NICKEL", 19), 24)
         , (("Brand#21", "MEDIUM ANODIZED COPPER", 3), 24)
         , (("Brand#22", "SMALL BRUSHED NICKEL", 3), 24)
         , (("Brand#22", "SMALL BURNISHED BRASS", 19), 24)
         , (("Brand#25", "MEDIUM BURNISHED COPPER ", 36), 24)
         , (("Brand#31", "PROMO POLISHED COPPER", 36), 24) ]

    r2 = [ (("Brand#11", "SMALL BRUSHED TIN", 19), 3)
         , (("Brand#15", "LARGE PLATED NICKEL", 45), 3)
         , (("Brand#15", "LARGE POLISHED NICKEL", 9), 3)
         , (("Brand#21", "PROMO BURNISHED STEEL", 45), 3)
         , (("Brand#22", "STANDARD PLATED STEEL", 23), 3)
         , (("Brand#25", "LARGE PLATED STEEL", 19), 3)
         , (("Brand#32", "STANDARD ANODIZED COPPER", 23), 3)
         , (("Brand#33", "SMALL ANODIZED BRASS", 9), 3)
         , (("Brand#35", "MEDIUM ANODIZED TIN", 19), 3)
         , (("Brand#51", "SMALL PLATED BRASS", 23), 3)
         , (("Brand#52", "MEDIUM BRUSHED BRASS", 45), 3)
         , (("Brand#53", "MEDIUM BRUSHED TIN", 45), 3)
         , (("Brand#54", "ECONOMY POLISHED BRASS", 9), 3)
         , (("Brand#55", "PROMO PLATED BRASS", 19), 3)
         , (("Brand#55", "STANDARD PLATED TIN", 49), 3) ]

q17Test :: Backend c => c -> H.Assertion
q17Test = makeEqAssertion "q17" q17Default res
  where
    res = 348406.05

q18Test :: Backend c => c -> H.Assertion
q18Test = makeEqAssertion "q18" q18Default res
  where
    res = [ (("Customer#000128120", 128120, 4722021, C.fromGregorian 1994 04 07, 544089.09), 323.00)
          , (("Customer#000144617", 144617, 3043270, C.fromGregorian 1997 02 12, 530604.44), 317.00)
          , (("Customer#000013940", 13940, 2232932, C.fromGregorian 1997 04 13, 522720.61), 304.00)
          , (("Customer#000066790", 66790, 2199712, C.fromGregorian 1996 09 30, 515531.82), 327.00)
          , (("Customer#000046435", 46435, 4745607, C.fromGregorian 1997 07 03, 508047.99), 309.00)
          , (("Customer#000015272", 15272, 3883783, C.fromGregorian 1993 07 28, 500241.33), 302.00)
          , (("Customer#000146608", 146608, 3342468, C.fromGregorian 1994 06 12, 499794.58), 303.00)
          , (("Customer#000096103", 96103, 5984582, C.fromGregorian 1992 03 16, 494398.79), 312.00)
          , (("Customer#000024341", 24341, 1474818, C.fromGregorian 1992 11 15, 491348.26), 302.00)
          , (("Customer#000137446", 137446, 5489475, C.fromGregorian 1997 05 23, 487763.25), 311.00)
          , (("Customer#000107590", 107590, 4267751, C.fromGregorian 1994 11 04, 485141.38), 301.00)
          , (("Customer#000050008", 50008, 2366755, C.fromGregorian 1996 12 09, 483891.26), 302.00)
          , (("Customer#000015619", 15619, 3767271, C.fromGregorian 1996 08 07, 480083.96), 318.00)
          , (("Customer#000077260", 77260, 1436544, C.fromGregorian 1992 09 12, 479499.43), 307.00)
          , (("Customer#000109379", 109379, 5746311, C.fromGregorian 1996 10 10, 478064.11), 302.00)
          , (("Customer#000054602", 54602, 5832321, C.fromGregorian 1997 02 09, 471220.08), 307.00)
          , (("Customer#000105995", 105995, 2096705, C.fromGregorian 1994 07 03, 469692.58), 307.00)
          , (("Customer#000148885", 148885, 2942469, C.fromGregorian 1992 05 31, 469630.44), 313.00)
          , (("Customer#000114586", 114586, 551136, C.fromGregorian 1993 05 19, 469605.59), 308.00)
          , (("Customer#000105260", 105260, 5296167, C.fromGregorian 1996 09 06, 469360.57), 303.00)
          , (("Customer#000147197", 147197, 1263015, C.fromGregorian 1997 02 02, 467149.67), 320.00)
          , (("Customer#000064483", 64483, 2745894, C.fromGregorian 1996 07 04, 466991.35), 304.00)
          , (("Customer#000136573", 136573, 2761378, C.fromGregorian 1996 05 31, 461282.73), 301.00)
          , (("Customer#000016384", 16384, 502886, C.fromGregorian 1994 04 12, 458378.92), 312.00)
          , (("Customer#000117919", 117919, 2869152, C.fromGregorian 1996 06 20, 456815.92), 317.00)
          , (("Customer#000012251", 12251, 735366, C.fromGregorian 1993 11 24, 455107.26), 309.00)
          , (("Customer#000120098", 120098, 1971680, C.fromGregorian 1995 06 14, 453451.23), 308.00)
          , (("Customer#000066098", 66098, 5007490, C.fromGregorian 1992 08 07, 453436.16), 304.00)
          , (("Customer#000117076", 117076, 4290656, C.fromGregorian 1997 02 05, 449545.85), 301.00)
          , (("Customer#000129379", 129379, 4720454, C.fromGregorian 1997 06 07, 448665.79), 303.00)
          , (("Customer#000126865", 126865, 4702759, C.fromGregorian 1994 11 07, 447606.65), 320.00)
          , (("Customer#000088876", 88876, 983201, C.fromGregorian 1993 12 30, 446717.46), 304.00)
          , (("Customer#000036619", 36619, 4806726, C.fromGregorian 1995 01 17, 446704.09), 328.00)
          , (("Customer#000141823", 141823, 2806245, C.fromGregorian 1996 12 29, 446269.12), 310.00)
          , (("Customer#000053029", 53029, 2662214, C.fromGregorian 1993 08 13, 446144.49), 302.00)
          , (("Customer#000018188", 18188, 3037414, C.fromGregorian 1995 01 25, 443807.22), 308.00)
          , (("Customer#000066533", 66533, 29158, C.fromGregorian 1995 10 21, 443576.50), 305.00)
          , (("Customer#000037729", 37729, 4134341, C.fromGregorian 1995 06 29, 441082.97), 309.00)
          , (("Customer#000003566", 3566, 2329187, C.fromGregorian 1998 01 04, 439803.36), 304.00)
          , (("Customer#000045538", 45538, 4527553, C.fromGregorian 1994 05 22, 436275.31), 305.00)
          , (("Customer#000081581", 81581, 4739650, C.fromGregorian 1995 11 04, 435405.90), 305.00)
          , (("Customer#000119989", 119989, 1544643, C.fromGregorian 1997 09 20, 434568.25), 320.00)
          , (("Customer#000003680", 3680, 3861123, C.fromGregorian 1998 07 03, 433525.97), 301.00)
          , (("Customer#000113131", 113131, 967334, C.fromGregorian 1995 12 15, 432957.75), 301.00)
          , (("Customer#000141098", 141098, 565574, C.fromGregorian 1995 09 24, 430986.69), 301.00)
          , (("Customer#000093392", 93392, 5200102, C.fromGregorian 1997 01 22, 425487.51), 304.00)
          , (("Customer#000015631", 15631, 1845057, C.fromGregorian 1994 05 12, 419879.59), 302.00)
          , (("Customer#000112987", 112987, 4439686, C.fromGregorian 1996 09 17, 418161.49), 305.00)
          , (("Customer#000012599", 12599, 4259524, C.fromGregorian 1998 02 12, 415200.61), 304.00)
          , (("Customer#000105410", 105410, 4478371, C.fromGregorian 1996 03 05, 412754.51), 302.00)
          , (("Customer#000149842", 149842, 5156581, C.fromGregorian 1994 05 30, 411329.35), 302.00)
          , (("Customer#000010129", 10129, 5849444, C.fromGregorian 1994 03 21, 409129.85), 309.00)
          , (("Customer#000069904", 69904, 1742403, C.fromGregorian 1996 10 19, 408513.00), 305.00)
          , (("Customer#000017746", 17746, 6882, C.fromGregorian 1997 04 09, 408446.93), 303.00)
          , (("Customer#000013072", 13072, 1481925, C.fromGregorian 1998 03 15, 399195.47), 301.00)
          , (("Customer#000082441", 82441, 857959, C.fromGregorian 1994 02 07, 382579.74), 305.00)
          , (("Customer#000088703", 88703, 2995076, C.fromGregorian 1994 01 30, 363812.12), 302.00) ]

q19Test :: Backend c => c -> H.Assertion
q19Test = makeEqAssertion "q19" q19Default res
  where
    res = 3083843.0578

q20Test :: Backend c => c -> H.Assertion
q20Test = makeEqAssertion "q20" q20Default res
  where
    res = [ ("Supplier#000000020", "iybAE,RmTymrZVYaFZva2SH,j")
          , ("Supplier#000000091", "YV45D7TknOOZ7q9QxkyGUapU1oOWU6q3")
          , ("Supplier#000000205", "rF uV8d0JNEk")
          , ("Supplier#000000285", "Br7e1nnt1yxrw6ImgpJ7YdhFDjuBf")
          , ("Supplier#000000287", "7a9SP7qW5Yku5PvSg")
          , ("Supplier#000000354", "w8fOo5W,aS")
          , ("Supplier#000000378", "FfbhyCxWvcPrO8ltp9")
          , ("Supplier#000000402", "i9Sw4DoyMhzhKXCH9By,AYSgmD")
          , ("Supplier#000000530", "0qwCMwobKY OcmLyfRXlagA8ukENJv,")
          , ("Supplier#000000555", "TfB,a5bfl3Ah 3Z 74GqnNs6zKVGM")
          , ("Supplier#000000640", "mvvtlQKsTOsJj5Ihk7,cq")
          , ("Supplier#000000729", "pqck2ppy758TQpZCUAjPvlU55K3QjfL7Bi")
          , ("Supplier#000000736", "l6i2nMwVuovfKnuVgaSGK2rDy65DlAFLegiL7")
          , ("Supplier#000000761", "zlSLelQUj2XrvTTFnv7WAcYZGvvMTx882d4")
          , ("Supplier#000000887", "urEaTejH5POADP2ARrf")
          , ("Supplier#000000935", "ij98czM 2KzWe7dDTOxB8sq0UfCdvrX")
          , ("Supplier#000000975", ",AC e,tBpNwKb5xMUzeohxlRn, hdZJo73gFQF8y")
          , ("Supplier#000001263", "rQWr6nf8ZhB2TAiIDIvo5Io")
          , ("Supplier#000001367", "42YSkFcAXMMcucsqeEefOE4HeCC")
          , ("Supplier#000001426", "bPOCc086oFm8sLtS,fGrH")
          , ("Supplier#000001446", "lch9HMNU1R7a0LIybsUodVknk6")
          , ("Supplier#000001500", "wDmF5xLxtQch9ctVu,")
          , ("Supplier#000001602", "uKNWIeafaM644")
          , ("Supplier#000001626", "UhxNRzUu1dtFmp0")
          , ("Supplier#000001682", "pXTkGxrTQVyH1Rr")
          , ("Supplier#000001700", "7hMlCof1Y5zLFg")
          , ("Supplier#000001726", "TeRY7TtTH24sEword7yAaSkjx8")
          , ("Supplier#000001730", "Rc8e,1Pybn r6zo0VJIEiD0UD vhk")
          , ("Supplier#000001746", "qWsendlOekQG1aW4uq06uQaCm51se8lirv7 hBRd")
          , ("Supplier#000001806", "M934fuZSnLW")
          , ("Supplier#000001855", "MWk6EAeozXb")
          , ("Supplier#000001931", "FpJbMU2h6ZR2eBv8I9NIxF")
          , ("Supplier#000002022", " dwebGX7Id2pc25YvY33")
          , ("Supplier#000002036", "20ytTtVObjKUUI2WCB0A")
          , ("Supplier#000002096", "kuxseyLtq QPLXxm9ZUrnB6Kkh92JtK5cQzzXNU")
          , ("Supplier#000002117", "MRtkgKolHJ9Wh X9J,urANHKDzvjr")
          , ("Supplier#000002204", "uYmlr46C06udCqanj0KiRsoTQakZsEyssL")
          , ("Supplier#000002218", "nODZw5q4dx kp0K5")
          , ("Supplier#000002243", "nSOEV3JeOU79")
          , ("Supplier#000002245", "hz2qWXWVjOyKhqPYMoEwz6zFkrTaDM")
          , ("Supplier#000002282", "ES21K9dxoW1I1TzWCj7ekdlNwSWnv1Z  6mQ,BKn")
          , ("Supplier#000002303", "nCoWfpB6YOymbgOht7ltfklpkHl")
          , ("Supplier#000002331", "WRh2w5WFvRg7Z0S1AvSvHCL")
          , ("Supplier#000002373", "RzHSxOTQmElCjxIBiVA52Z JB58rJhPRylR")
          , ("Supplier#000002419", "qydBQd14I5l5mVXa4fYY")
          , ("Supplier#000002571", "JZUugz04c iJFLrlGsz9O N,W 1rVHNIReyq")
          , ("Supplier#000002585", "CsPoKpw2QuTY4AV1NkWuttneIa4SN")
          , ("Supplier#000002629", "0Bw,q5Zp8su9XrzoCngZ3cAEXZwZ")
          , ("Supplier#000002721", "HVdFAN2JHMQSpKm")
          , ("Supplier#000002730", "lIFxR4fzm31C6,muzJwl84z")
          , ("Supplier#000002775", "yDclaDaBD4ihH")
          , ("Supplier#000002799", "lwr, 6L3gdfc79PQut,4XO6nQsTJY63cAyYO")
          , ("Supplier#000002934", "m,trBENywSArwg3DhB")
          , ("Supplier#000002941", "Naddba 8YTEKekZyP0")
          , ("Supplier#000003028", "jouzgX0WZjhNMWLaH4fy")
          , ("Supplier#000003095", "HxON3jJhUi3zjt,r mTD")
          , ("Supplier#000003143", "hdolgh608uTkHh7t6qfSqkifKaiFjnCH")
          , ("Supplier#000003185", "hMa535Cbf2mj1Nw4OWOKWVrsK0VdDkJURrdjSIJe")
          , ("Supplier#000003189", "DWdPxt7 RnkZv6VOByR0em")
          , ("Supplier#000003201", "E87yws6I,t0qNs4QW7UzExKiJnJDZWue")
          , ("Supplier#000003213", "pxrRP4irQ1VoyfQ,dTf3")
          , ("Supplier#000003275", "9xO4nyJ2QJcX6vGf")
          , ("Supplier#000003288", "EDdfNt7E5Uc,xLTupoIgYL4yY7ujh,")
          , ("Supplier#000003314", "jnisU8MzqO4iUB3zsPcrysMw3DDUojS4q7LD")
          , ("Supplier#000003373", "iy8VM48ynpc3N2OsBwAvhYakO2us9R1bi")
          , ("Supplier#000003421", "Sh3dt9W5oeofFWovnFhrg,")
          , ("Supplier#000003422", "DJoCEapUeBXoV1iYiCcPFQvzsTv2ZI960")
          , ("Supplier#000003441", "zvFJIzS,oUuShHjpcX")
          , ("Supplier#000003590", "sy79CMLxqb,Cbo")
          , ("Supplier#000003607", "lNqFHQYjwSAkf")
          , ("Supplier#000003625", "qY588W0Yk5iaUy1RXTgNrEKrMAjBYHcKs")
          , ("Supplier#000003723", "jZEp0OEythCLcS OmJSrFtxJ66bMlzSp")
          , ("Supplier#000003849", "KgbZEaRk,6Q3mWvwh6uptrs1KRUHg 0")
          , ("Supplier#000003894", "vvGC rameLOk")
          , ("Supplier#000003941", "Pmb05mQfBMS618O7WKqZJ 9vyv")
          , ("Supplier#000004059", "umEYZSq9RJ2WEzdsv9meU8rmqwzVLRgiZwC")
          , ("Supplier#000004207", "tF64pwiOM4IkWjN3mS,e06WuAjLx")
          , ("Supplier#000004236", "dl,HPtJmGipxYsSqn9wmqkuWjst,mCeJ8O6T")
          , ("Supplier#000004278", "bBddbpBxIVp Di9")
          , ("Supplier#000004281", "1OwPHh Pgiyeus,iZS5eA23JDOipwk")
          , ("Supplier#000004304", "hQCAz59k,HLlp2CKUrcBIL")
          , ("Supplier#000004346", "S3076LEOwo")
          , ("Supplier#000004406", "Ah0ZaLu6VwufPWUz,7kbXgYZhauEaHqGIg")
          , ("Supplier#000004430", "yvSsKNSTL5HLXBET4luOsPNLxKzAMk")
          , ("Supplier#000004527", "p pVXCnxgcklWF6A1o3OHY3qW6")
          , ("Supplier#000004655", "67NqBc4 t3PG3F8aO IsqWNq4kGaPowYL")
          , ("Supplier#000004851", "Rj,x6IgLT7kBL99nqp")
          , ("Supplier#000004884", "42Z1uLye9nsn6aTGBNd dI8 x")
          , ("Supplier#000004975", "GPq5PMKY6Wy")
          , ("Supplier#000005076", "Xl7h9ifgvIHmqxFLgWfHK4Gjav BkP")
          , ("Supplier#000005195", "Woi3b2ZaicPh ZSfu1EfXhE")
          , ("Supplier#000005256", "Onc3t57VAMchm,pmoVLaU8bONni9NsuaM PzMMFz")
          , ("Supplier#000005257", "f9g8SEHB7obMj3QXAjXS2vfYY22")
          , ("Supplier#000005300", "gXG28YqpxU")
          , ("Supplier#000005323", "tMCkdqbDoyNo8vMIkzjBqYexoRAuv,T6 qzcu")
          , ("Supplier#000005386", "Ub6AAfHpWLWP")
          , ("Supplier#000005426", "9Dz2OVT1q sb4BK71ljQ1XjPBYRPvO")
          , ("Supplier#000005465", "63cYZenZBRZ613Q1FaoG0,smnC5zl9")
          , ("Supplier#000005484", "saFdOR qW7AFY,3asPqiiAa11Mo22pCoN0BtPrKo")
          , ("Supplier#000005505", "d2sbjG43KwMPX")
          , ("Supplier#000005506", "On f5ypzoWgB")
          , ("Supplier#000005631", "14TVrjlzo2SJEBYCDgpMwTlvwSqC")
          , ("Supplier#000005642", "ZwKxAv3V40tW E8P7Qwu,zlu,kPsL")
          , ("Supplier#000005686", "f2RBKec2T1NIi7yS M")
          , ("Supplier#000005730", "5rkb0PSews HvxkL8JaD41UpnSF2cg8H1")
          , ("Supplier#000005736", "2dq XTYhtYWSfp")
          , ("Supplier#000005737", "dmEWcS32C3kx,d,B95 OmYn48")
          , ("Supplier#000005797", ",o,OebwRbSDmVl9gN9fpWPCiqB UogvlSR")
          , ("Supplier#000005875", "lK,sYiGzB94hSyHy9xvSZFbVQNCZe2LXZuGbS")
          , ("Supplier#000005974", "REhR5jE,lLusQXvf54SwYySgsSSVFhu")
          , ("Supplier#000006059", "4m0cv8MwJ9yX2vlwI Z")
          , ("Supplier#000006065", "UiI2Cy3W4Tu5sLk LuvXLRy6KihlGv")
          , ("Supplier#000006093", "KJNUg1odUT2wtCS2s6PrH3D6")
          , ("Supplier#000004871", ",phpt6AWEnUS8t4Avb50rF") ]

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

q22Test :: Backend c => c -> H.Assertion
q22Test = makeEqAssertion "q22" q22Default res
  where
    res = [ ("13", 888, 6737713.99)
          , ("17", 861, 6460573.72)
          , ("18", 964, 7236687.40)
          , ("23", 892, 6701457.95)
          , ("29", 948, 7158866.63)
          , ("30", 909, 6808436.13)
          , ("31", 922, 6806670.18) ]

tests :: Backend c => c -> TestTree
tests c = testGroup "TPC-H standard tests"
    [ TH.testCase "q1" (q1Test c)
    , TH.testCase "q2" (q2Test c)
    , TH.testCase "q3" (q3Test c)
    , TH.testCase "q4" (q4Test c)
    , TH.testCase "q5" (q5Test c)
    , TH.testCase "q6" (q6Test c)
    , TH.testCase "q7" (q7Test c)
    , TH.testCase "q8" (q8Test c)
    , TH.testCase "q9" (q9Test c)
    , TH.testCase "q10" (q10Test c)
    , TH.testCase "q11" (q11Test c)
    , TH.testCase "q12" (q12Test c)
    , TH.testCase "q13" (q13Test c)
    , TH.testCase "q14" (q14Test c)
    , TH.testCase "q15" (q15Test c)
    , TH.testCase "q16" (q16Test c)
    , TH.testCase "q17" (q17Test c)
    , TH.testCase "q18" (q18Test c)
    -- test disabled: DSH unnesting fail.
    -- , TH.testCase "q19" (q19Test c)
    -- tests disabled: PostgreSQL currently (13-01-16) generates a really bad
    -- plan and the query does not run in acceptable time.
    -- , TH.testCase "q20" (q20Test c)
    -- , TH.testCase "q21" (q21Test c)
    , TH.testCase "q22" (q22Test c)
    ]

main :: IO ()
main = do
    args <- getArgs
    when ("--help" `elem` args) $ do
        putStrLn "Usage: test-tpch [tasty args] <dbname>"
        withArgs ["--help"] $ defaultMain $ testGroup "empty" []
        exitFailure
    let tfArgs = init args
        db     = last args
    conn <- sqlBackend <$> connectODBC ("DSN=" ++ db)
    withArgs tfArgs $ defaultMain (tests conn)
