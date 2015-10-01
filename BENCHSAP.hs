
module Main
where
import Data.List (groupBy,sortBy)
import Data.Time (getCurrentTime, diffUTCTime)
import DEMO_S5
import EXAMPLES (sapExplainState,sapSolutions)

runSMCDEL :: IO ()
runSMCDEL = do
  putStrLn "The solution is:"
  mapM_ (putStrLn . sapExplainState) sapSolutions

--possible pairs 1<x<y, x+y<=100
allpairs :: [(Int,Int)]
allpairs  = [(x,y)|x<-[2..100], y<-[2..100], x<y, x+y<=100]

alice, bob :: Agent
(alice,bob) = (Ag 0,Ag 1)

--initial pointed epistemic model
msnp :: EpistM (Int,Int)
msnp = Mo allpairs [alice,bob] [] rels allpairs where
  rels  = [ (alice,partWith (+)) , (bob,partWith (*)) ]
  partWith op = groupBy (\(x,y) (x',y') -> op x y == op x' y') $
    sortBy (\(x,y) (x',y') -> compare (op x y) (op x' y')) allpairs

fmrs1e, fmrp2e, fmrs3e :: Form (Int,Int)

--Sum says: I knew that you didn't know the two numbers.
fmrs1e = Kn alice (Conj [Disj[Ng (Info p),
                         Ng (Kn bob (Info p))]| p<-allpairs])

--Product says: Now I know the two numbers
fmrp2e = Conj [ Disj[Ng (Info p),
                     Kn bob (Info p) ] |p<-allpairs]

--Sum says: Now I know the two numbers too
fmrs3e = Conj [ Disj[Ng (Info p),
                     Kn alice (Info p) ] |p<-allpairs]

runDemoS5 :: IO ()
runDemoS5 = print $ updsPa msnp [fmrs1e, fmrp2e, fmrs3e]

main :: IO ()
main = do
  putStrLn "*** Running DEMO_S5 ***"
  start <- getCurrentTime
  runDemoS5
  end <- getCurrentTime
  putStrLn $ "This took " ++ show (end `diffUTCTime` start) ++ " seconds.\n"

  putStrLn "*** Running SMCDEL ***"
  start2 <- getCurrentTime
  runSMCDEL
  end2 <- getCurrentTime
  putStrLn $ "This took " ++ show (end2 `diffUTCTime` start2) ++ " seconds.\n"
