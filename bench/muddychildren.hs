module Main where

import Control.Monad (when)
import Criterion.Main
import qualified Criterion.Types
import qualified Data.ByteString.Lazy as BL
import Data.Char (isSpace)
import Data.Csv
import Data.Function
import Data.List
import Data.List.Split
import Data.Maybe
import Data.Scientific
import qualified Data.Vector as V
import Numeric
import System.Directory

import SMCDEL.Language
import SMCDEL.Examples.MuddyChildren
import SMCDEL.Internal.Help (apply)
import qualified SMCDEL.Explicit.DEMO_S5 as DEMO_S5
import qualified SMCDEL.Explicit.S5
import qualified SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.S5_CUDD
import qualified SMCDEL.Translations.S5
import qualified SMCDEL.Translations.K
import qualified SMCDEL.Other.MCTRIANGLE
import qualified SMCDEL.Symbolic.K

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
findNumberCacBDD = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.S5.evalViaBdd) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.S5.KnS (mudPs n) (SMCDEL.Symbolic.S5.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,SMCDEL.Symbolic.S5_CUDD.evalViaBdd) where
  cuddMudScnInit n m = ( SMCDEL.Symbolic.S5_CUDD.KnS (mudPs n) (SMCDEL.Symbolic.S5_CUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberTrans :: Int -> Int -> Int
findNumberTrans = findNumberWith (start,SMCDEL.Symbolic.S5.evalViaBdd) where
  start n m = SMCDEL.Translations.S5.kripkeToKns $ mudKrpInit n m

mudKrpInit :: Int -> Int -> SMCDEL.Explicit.S5.PointedModelS5
mudKrpInit n m = (SMCDEL.Explicit.S5.KrMS5 ws rel val, cur) where
  ws    = [0..(2^n-1)]
  rel   = [ (show i, erelFor i) | i <- [1..n] ] where
    erelFor i = sort $ map sort $
      groupBy ((==) `on` setForAt i) $
      sortOn (setForAt i) ws
    setForAt i s = delete (P i) $ setAt s
    setAt s = map fst $ filter snd (apply val s)
  val         = zip ws table
  ((cur,_):_) = filter (\(_,ass)-> sort (map fst $ filter snd ass) == [P 1..P m]) val
  table = foldl buildTable [[]] [P k | k<- [1..n]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

findNumberK :: Int -> Int -> Int
findNumberK = findNumberWith (mudBelScnInit, SMCDEL.Symbolic.K.evalViaBdd)

findNumberTransK :: Int -> Int -> Int
findNumberTransK = findNumberWith (start,SMCDEL.Symbolic.K.evalViaBdd) where
  start n m = SMCDEL.Translations.K.kripkeToBls $ mudGenKrpInit n m

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
  start = SMCDEL.Other.MCTRIANGLE.mcUpdate (SMCDEL.Other.MCTRIANGLE.mcModel (n-m,m)) (SMCDEL.Other.MCTRIANGLE.Qf SMCDEL.Other.MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> SMCDEL.Other.MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if SMCDEL.Other.MCTRIANGLE.eval curMod SMCDEL.Other.MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (SMCDEL.Other.MCTRIANGLE.mcUpdate curMod SMCDEL.Other.MCTRIANGLE.nobodyknows)
    else count

main :: IO ()
main = prepareMain >> benchMain >> convertMain

benchMain :: IO ()
benchMain = defaultMainWith myConfig (map mybench
  [ ("Triangle"  , findNumberTriangle  , [7..40] )
  , ("CacBDD"    , findNumberCacBDD    , [3..40] )
  , ("CUDD"      , findNumberCUDD      , [3..40] )
  , ("K"         , findNumberK         , [3..12] )
  , ("DEMOS5"    , findNumberDemoS5    , [3..12] )
  , ("Trans"     , findNumberTrans     , [3..12] )
  , ("TransK"    , findNumberTransK    , [3..11] ) ])
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf (\n -> f n n) k
    myConfig = defaultConfig { Criterion.Types.csvFile = Just theCSVname }

theCSVname :: String
theCSVname = "muddychildren-results.csv"

prepareMain :: IO ()
prepareMain = do
  oldResults <- doesFileExist theCSVname
  when oldResults $ do
    putStrLn "moving away old results!"
    renameFile theCSVname ("OLD-results-" ++ theCSVname)
    oldDATfile <- doesFileExist (theCSVname ++ ".dat")
    when oldDATfile $ removeFile (theCSVname ++ ".dat")

convertMain :: IO ()
convertMain = do
  putStrLn "Reading muddychildren-results.csv and converting to .dat for pgfplots."
  c <- BL.readFile theCSVname
  case decode NoHeader c of
    Left e -> error $ "could not parse the csv file:" ++ show e
    Right csv -> do
      let results = map (parseLine . take 2) $ tail $ V.toList (csv :: V.Vector [String])
      let columns = nub.sort $ map (fst.fst) results
      let firstLine = longifyTo 5 "n" ++ dropWhileEnd isSpace (concatMap longify columns)
      let resAt n col = longify $ fromMaybe "nan" $ Data.List.lookup (col,n) results
      let resultrow n = concatMap (resAt n) columns
      let firstcol = nub.sort $ map (snd.fst) results
      let resultrows = map (\n -> longifyTo 5 (show n) ++ dropWhileEnd isSpace (resultrow n)) firstcol
      writeFile (theCSVname ++ ".dat") (intercalate "\n" (firstLine:resultrows) ++ "\n")
  where
    parseLine [namestr,numberstr] = case splitOn "/" namestr of
      [name,nstr] -> ((name,n),valuestr) where
        n = read nstr :: Integer
        value = toRealFloat (read numberstr :: Scientific) :: Double
        valuestr = Numeric.showFFloat (Just 7) value ""
      _ -> error $ "could not parse this case: " ++ namestr
    parseLine l = error $ "could not parse this line:\n  " ++ show l
    longify = longifyTo 14
    longifyTo n s = s ++ replicate (n - length s) ' '
