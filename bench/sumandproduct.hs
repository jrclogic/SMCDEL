module Main (main) where
import Criterion.Main
import Data.List (groupBy,sortBy)
import Data.Time (getCurrentTime, diffUTCTime)
import System.Environment (getArgs)
import SMCDEL.Explicit.DEMO_S5
import SMCDEL.Examples.SumAndProduct
import SMCDEL.Symbolic.S5

--possible pairs 1<x<y, x+y<=100
alice, bob :: Agent
(alice,bob) = (Ag 0,Ag 1)

--initial pointed epistemic model
msnp :: EpistM (Int,Int)
msnp = Mo pairs [alice,bob] [] rels pairs where
  rels  = [ (alice,partWith (+)) , (bob,partWith (*)) ]
  partWith op = groupBy (\(x,y) (x',y') -> op x y == op x' y') $
    sortBy (\(x,y) (x',y') -> compare (op x y) (op x' y')) pairs

fmrs1e, fmrp2e, fmrs3e :: DemoForm (Int,Int)

--Sum says: I knew that you didn't know the two numbers.
fmrs1e = Kn alice (Conj [Disj[Ng (Info p),
                         Ng (Kn bob (Info p))]| p <- pairs])

--Product says: Now I know the two numbers
fmrp2e = Conj [ Disj[Ng (Info p),
                     Kn bob (Info p) ] | p <- pairs]

--Sum says: Now I know the two numbers too
fmrs3e = Conj [ Disj[Ng (Info p),
                     Kn alice (Info p) ] | p <- pairs]

main :: IO ()
main = do
  args <- getArgs
  if args == ["checkingOnly"]
    then do
      putStrLn "Benchmarking only the checking, without model generation."
      benchCheckingOnly
    else do
      putStrLn "Benchmarking the complete run."
      benchAllOnce

benchAllOnce :: IO ()
benchAllOnce = do
  putStrLn "*** Running DEMO_S5 ***"
  start <- getCurrentTime
  print $ updsPa msnp [fmrs1e, fmrp2e, fmrs3e]
  end <- getCurrentTime
  putStrLn $ "This took " ++ show (end `diffUTCTime` start) ++ " seconds.\n"

  putStrLn "*** Running SMCDEL ***"
  start2 <- getCurrentTime
  mapM_ (putStrLn . sapExplainState) sapSolutions
  end2 <- getCurrentTime
  putStrLn $ "This took " ++ show (end2 `diffUTCTime` start2) ++ " seconds.\n"

benchCheckingOnly :: IO ()
benchCheckingOnly = defaultMain [
  bgroup "checkingOnly"
    [ bench "DEMO-S5" $ nf (show . updsPa msnp) [fmrs1e, fmrp2e, fmrs3e]
    , bench "SMCDEL"  $ nf (sapExplainState . head . whereViaBdd sapKnStruct) sapProtocol
    ]
  ]
