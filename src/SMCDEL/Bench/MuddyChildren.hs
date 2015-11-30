
module Main (main) where
import Control.Monad
import Data.List
import Data.Time (getCurrentTime, NominalDiffTime, diffUTCTime)
import System.Environment (getArgs)
import System.IO (stdout, hSetBuffering, BufferMode(NoBuffering))
import SMCDEL.Language
import SMCDEL.Examples
import qualified SMCDEL.Explicit.DEMO_S5
import qualified SMCDEL.Symbolic.HasCacBDD
import qualified SMCDEL.Symbolic.CUDD
import qualified SMCDEL.Symbolic.Robbed
import qualified SMCDEL.Symbolic.NooBDD
import qualified SMCDEL.Symbolic.SatZ3
import qualified SMCDEL.Other.MCTRIANGLE

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

findNumberCacBDD :: Int -> Int -> Int
findNumberCacBDD = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.HasCacBDD.evalViaBdd) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.HasCacBDD.KnS (mudPs n) (SMCDEL.Symbolic.HasCacBDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,SMCDEL.Symbolic.CUDD.evalViaBdd) where
  cuddMudScnInit n m = ( SMCDEL.Symbolic.CUDD.KnS (mudPs n) (SMCDEL.Symbolic.CUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberRobBDD :: Int -> Int -> Int
findNumberRobBDD = findNumberWith (robMudScnInit,SMCDEL.Symbolic.Robbed.evalViaBdd) where
  robMudScnInit n m = ( SMCDEL.Symbolic.Robbed.KnS (mudPs n) (SMCDEL.Symbolic.Robbed.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberNooBDD :: Int -> Int -> Int
findNumberNooBDD = findNumberWith (nooMudScnInit,SMCDEL.Symbolic.NooBDD.evalViaBdd) where
  nooMudScnInit n m = ( SMCDEL.Symbolic.NooBDD.KnS (mudPs n) (SMCDEL.Symbolic.NooBDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

findNumberZ3 :: Int -> Int -> Int
findNumberZ3 = findNumberWith (z3MudScnInit,SMCDEL.Symbolic.SatZ3.evalViaZ3) where
  z3MudScnInit n m = ( SMCDEL.Symbolic.SatZ3.KnS (mudPs n) (SMCDEL.Symbolic.SatZ3.boolAstOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], [P 1 .. P m] )

mudDemoKrpInit :: Int -> Int -> SMCDEL.Explicit.DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = SMCDEL.Explicit.DEMO_S5.Mo states agents [] rels points where
  states = SMCDEL.Explicit.DEMO_S5.bTables n
  agents = map SMCDEL.Explicit.DEMO_S5.Ag [1..n]
  rels = [(SMCDEL.Explicit.DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- SMCDEL.Explicit.DEMO_S5.bTables (i-1),
                   tab2 <- SMCDEL.Explicit.DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemo :: Int -> Int -> Int
findNumberDemo n m = findNumberDemoLoop n m 0 start where
  start = SMCDEL.Explicit.DEMO_S5.updPa (mudDemoKrpInit n m) (SMCDEL.Explicit.DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> SMCDEL.Explicit.DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if SMCDEL.Explicit.DEMO_S5.isTrue curMod (SMCDEL.Explicit.DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (SMCDEL.Explicit.DEMO_S5.updPa curMod (SMCDEL.Explicit.DEMO_S5.dont n))
    else count

findNumberTriangle :: Int -> Int -> Int
findNumberTriangle n m = findNumberTriangleLoop 0 start where
  start = SMCDEL.Other.MCTRIANGLE.update (SMCDEL.Other.MCTRIANGLE.mcModel (n-m,m)) (SMCDEL.Other.MCTRIANGLE.Qf SMCDEL.Other.MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> SMCDEL.Other.MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if SMCDEL.Other.MCTRIANGLE.eval curMod SMCDEL.Other.MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (SMCDEL.Other.MCTRIANGLE.update curMod SMCDEL.Other.MCTRIANGLE.nobodyknows)
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
  args <- getArgs
  limit <- case args of
    [aInteger] | [(n,_)] <- reads aInteger -> return n
    _ -> do
      putStrLn "No maximum runtime given, defaulting to one second."
      return 1
  hSetBuffering stdout NoBuffering
  putStrLn $ "Initializing CacBDD: 40==" ++ show (findNumberCacBDD 41 41)
  putStrLn $ "Initializing CUDD: 40==" ++ show (findNumberCUDD 41 41)
  let methodList = [ ("Triangle  ", findNumberTriangle)
                   , ("HasCacBDD ", findNumberCacBDD  )
                   , ("CUDD      ", findNumberCUDD    )
                   , ("Robbed    ", findNumberRobBDD  )
                   , ("NooBDD    ", findNumberNooBDD  )
                   , ("DEMO-S5   ", findNumberDemo    )
                   , ("SatZ3     ", findNumberZ3      )
                   ]
  putStrLn $ "n\t" ++ concatMap ((++ "\t").fst) methodList
  mainLoop (zip (repeat True) (map snd methodList)) ([3..40]++[50,60,70,80,90,100]) limit
