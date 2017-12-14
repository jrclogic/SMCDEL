
module Main where
import Criterion.Main
import Data.Function
import Data.List
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import SMCDEL.Language
import SMCDEL.Examples
import SMCDEL.Internal.Help (apply,seteq)
import qualified SMCDEL.Explicit.DEMO_S5 as DEMO_S5
import qualified SMCDEL.Explicit.Simple
import qualified SMCDEL.Symbolic.HasCacBDD
import qualified SMCDEL.Symbolic.CUDD
import qualified SMCDEL.Translations
import qualified SMCDEL.Other.MCTRIANGLE
import qualified SMCDEL.Other.NonS5
import Data.Map.Strict (fromList)

checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

findNumberWith :: (Int -> Int -> a, a -> Form -> Bool) -> Int -> Int -> Int
findNumberWith (start,evalfunction) n m = k where
  k | loop 0 == (m-1) = m-1
    | otherwise       = error $ "wrong Muddy Children result: " ++ show (loop 0)
  loop count = if evalfunction (start n m) (PubAnnounce (father n) (checkForm n count))
    then loop (count+1)
    else count

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

findNumberCacBDD :: Int -> Int -> Int
findNumberCacBDD = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.HasCacBDD.evalViaBdd) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.HasCacBDD.KnS (mudPs n) (SMCDEL.Symbolic.HasCacBDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,SMCDEL.Symbolic.CUDD.evalViaBdd) where
  cuddMudScnInit n m = ( SMCDEL.Symbolic.CUDD.KnS (mudPs n) (SMCDEL.Symbolic.CUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberTrans :: Int -> Int -> Int
findNumberTrans = findNumberWith (start,SMCDEL.Symbolic.HasCacBDD.evalViaBdd) where
  start n m = SMCDEL.Translations.kripkeToKns $ mudKrpInit n m

mudKrpInit :: Int -> Int -> SMCDEL.Explicit.Simple.PointedModel
mudKrpInit n m = (SMCDEL.Explicit.Simple.KrM ws rel val, cur) where
  ws    = [0..(2^n-1)]
  rel   = [ (show i, erelFor i) | i <- [1..n] ] where
    erelFor i = sort $ map sort $
      groupBy ((==) `on` setForAt i) $
      sortBy (comparing (setForAt i)) ws
    setForAt i s = delete (P i) $ setAt s
    setAt s = map fst $ filter snd (apply val s)
  val         = zip ws table
  ((cur,_):_) = filter (\(_,ass)-> sort (map fst $ filter snd ass) == [P 1..P m]) val
  table = foldl buildTable [[]] [P k | k<- [1..n]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

findNumberNonS5 :: Int -> Int -> Int
findNumberNonS5 = findNumberWith
  (SMCDEL.Other.NonS5.mudGenScnInit,SMCDEL.Other.NonS5.evalViaBdd)

findNumberNonS5Trans :: Int -> Int -> Int
findNumberNonS5Trans = findNumberWith (start,SMCDEL.Other.NonS5.evalViaBdd) where
  start n m = SMCDEL.Other.NonS5.genKrp2Kns $ SMCDEL.Other.NonS5.mudGenKrpInit n m

mudDemoKrpInit :: Int -> Int -> DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = DEMO_S5.Mo states agents [] rels points where
  states = DEMO_S5.bTables n
  agents = map DEMO_S5.Ag [1..n]
  rels = [(DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- DEMO_S5.bTables (i-1),
                   tab2 <- DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemoS5 :: Int -> Int -> Int
findNumberDemoS5 n m = findNumberDemoLoop n m 0 start where
  start = DEMO_S5.updPa (mudDemoKrpInit n m) (DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if DEMO_S5.isTrue curMod (DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (DEMO_S5.updPa curMod (DEMO_S5.dont n))
    else count

findNumberTriangle :: Int -> Int -> Int
findNumberTriangle n m = findNumberTriangleLoop 0 start where
  start = SMCDEL.Other.MCTRIANGLE.update (SMCDEL.Other.MCTRIANGLE.mcModel (n-m,m)) (SMCDEL.Other.MCTRIANGLE.Qf SMCDEL.Other.MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> SMCDEL.Other.MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if SMCDEL.Other.MCTRIANGLE.eval curMod SMCDEL.Other.MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (SMCDEL.Other.MCTRIANGLE.update curMod SMCDEL.Other.MCTRIANGLE.nobodyknows)
    else count

main :: IO ()
main = defaultMain (map mybench
  [ ("Triangle"  , findNumberTriangle  , [7..40] )
  , ("CacBDD"    , findNumberCacBDD    , [3..40] )
  , ("CUDD"      , findNumberCUDD      , [3..40] )
  , ("NonS5"     , findNumberNonS5     , [3..12] )
  , ("DEMOS5"    , findNumberDemoS5    , [3..12] )
  , ("Trans"     , findNumberTrans     , [3..12] )
  , ("NonS5Trans", findNumberNonS5Trans, [3..11] ) ])
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf (\n -> f n n) k
