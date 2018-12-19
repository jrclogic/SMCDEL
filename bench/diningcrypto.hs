module Main (main) where

import Control.Monad (when)
import Data.Time (diffUTCTime,getCurrentTime,NominalDiffTime)
import System.Environment (getArgs)
import System.IO (hSetBuffering,BufferMode(NoBuffering),stdout)
import Text.Printf

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Examples.DiningCrypto

benchDcCheckForm :: Int -> Form
benchDcCheckForm n =
  PubAnnounceW (Xor [genDcReveal n i | i<-[1..n] ]) $
  -- pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $ -- slow!
    Impl (Neg (PrpF $ P 1)) $
      Disj [ K "1" (Conj [Neg $ PrpF $ P k | k <- [1..n]  ])
           , Conj [ K "1" (Disj [ PrpF $ P k | k <- [2..n] ])
                  , Conj [ Neg $ K "1" (PrpF $ P k) | k <- [2..n] ] ] ]

benchDcValid :: Int -> Bool
benchDcValid n = validViaBdd (genDcKnsInit n) (benchDcCheckForm n)

dcTimeThis :: Int -> IO NominalDiffTime
dcTimeThis n = do
  start <- getCurrentTime
  let mykns@(KnS props _ _) = genDcKnsInit n
  putStr $ show (length props) ++ "\t"
  putStr $ show (length $ show mykns) ++ "\t"
  putStr $ show (length $ show $ benchDcCheckForm n) ++ "\t"
  if benchDcValid n then do
    end <- getCurrentTime
    return (end `diffUTCTime` start)
  else
    error "Wrong result."

mainLoop :: [Int] -> Int -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n:ns) limit = do
  putStr $ show n ++ "\t"
  result <- dcTimeThis n
  printf "%.4f\n" (realToFrac result :: Double)
  when (result <= fromIntegral limit) $ mainLoop ns limit

main :: IO ()
main = do
  args <- getArgs
  hSetBuffering stdout NoBuffering
  limit <- case args of
    [aInteger] | [(n,_)] <- reads aInteger -> return n
    _ -> do
      putStrLn "No maximum runtime given, defaulting to one second."
      return 1
  putStrLn $ "n" ++ "\tn(prps)"++ "\tsz(KNS)"++ "\tsz(frm)" ++ "\ttime"
  mainLoop (3:4:(5 : map (10*) [1..])) limit
