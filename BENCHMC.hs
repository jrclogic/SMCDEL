
module Main (main) where
import Control.Monad
import Data.List
import Data.Time (getCurrentTime, NominalDiffTime, diffUTCTime)
import System.Environment (getArgs)
import System.IO (stdout, hSetBuffering, BufferMode(NoBuffering))
import DELLANG
import EXAMPLES
import qualified DEMO_S5
import qualified KNSCAC
import qualified KNSCUDD
import qualified KNSROB
import qualified KNSNOO
import qualified MCTRIANGLE

checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

findNumberWith :: (Int -> Int -> a, a -> Form -> Bool) -> Int -> Int -> Int
findNumberWith (start,evalfunction) n m = loop 0 where
  loop count = if evalfunction (start n m) (PubAnnounce (father n) (checkForm n count))
    then loop (count+1)
    else count

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

findNumberCacBdd :: Int -> Int -> Int
findNumberCacBdd = findNumberWith (cacMudScnInit,KNSCAC.evalViaBdd) where
  cacMudScnInit n m = ( KNSCAC.KnS (mudPs n) (KNSCAC.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,KNSCUDD.evalViaBdd) where
  cuddMudScnInit n m = ( KNSCUDD.KnS (mudPs n) (KNSCUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberRobBdd :: Int -> Int -> Int
findNumberRobBdd = findNumberWith (robMudScnInit,KNSROB.evalViaBdd) where
  robMudScnInit n m = ( KNSROB.KnS (mudPs n) (KNSROB.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberNooBdd :: Int -> Int -> Int
findNumberNooBdd = findNumberWith (nooMudScnInit,KNSNOO.evalViaBdd) where
  nooMudScnInit n m = ( KNSNOO.KnS (mudPs n) (KNSNOO.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

mudDemoKrpInit :: Int -> Int -> DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = DEMO_S5.Mo states agents [] rels points where
  states = DEMO_S5.bTables n
  agents = map DEMO_S5.Ag [1..n]
  rels = [(DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- DEMO_S5.bTables (i-1),
                   tab2 <- DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemo :: Int -> Int -> Int
findNumberDemo n m = findNumberDemoLoop n m 0 start where
  start = DEMO_S5.updPa (mudDemoKrpInit n m) (DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if DEMO_S5.isTrue curMod (DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (DEMO_S5.updPa curMod (DEMO_S5.dont n))
    else count

findNumberTriangle :: Int -> Int -> Int
findNumberTriangle n m = findNumberTriangleLoop 0 start where
  start = MCTRIANGLE.update (MCTRIANGLE.mcModel (n-m,m)) (MCTRIANGLE.Qf MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if MCTRIANGLE.eval curMod MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (MCTRIANGLE.update curMod MCTRIANGLE.nobodyknows)
    else count

timeWith :: Int -> Int -> (Int -> Int -> Int) -> IO NominalDiffTime
timeWith n m function = do
  start <- getCurrentTime
  if function n m == (m - 1)
    then do end <- getCurrentTime
            return (end `diffUTCTime` start)
    else error "Wrong result."

mainLoop :: [(Bool, Int -> Int -> Int)] -> [Int] -> Int -> IO ()
mainLoop _  [] _ = putStrLn ""
mainLoop fs (n:ns) limit = do
  putStr $ show n ++ "\t"
  results <- mapM (\(bit,f) ->
    if bit then do
      result <- timeWith n n f
      putStr $ init (show result) ++ replicate (9 - length (show result)) '0' ++ "\t"
      return result
    else do
      putStr "nan      \t"
      return 0
    ) fs
  putStrLn ""
  let newfs = map (\((bit,f),t) -> (bit && (t<= fromIntegral limit), f)) (zip fs results)
  when (any fst newfs) $ mainLoop newfs ns limit

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  putStrLn $ "Initializing CacBDD: 40==" ++ show (findNumberCacBdd 41 41)
  putStrLn $ "Initializing CUDD: 40==" ++ show (findNumberCUDD 41 41)
  putStrLn $ "n\t" ++ concatMap (++ "\t") ["TRIANGLE","KNSCAC  ","KNSCUDD ", "KNSROB  ","KNSNOO  ","DEMO-S5 "]
  let allfs = [findNumberTriangle, findNumberCacBdd, findNumberCUDD, findNumberRobBdd, findNumberNooBdd, findNumberDemo]
  args <- getArgs
  case args of
    [aInteger] | [(n,_)] <- reads aInteger ->
      mainLoop (zip (repeat True) allfs) ([3..40]++[50,60,70,80,90,100]) n
    _ -> error "Please give a maximum runtime as an argument."
