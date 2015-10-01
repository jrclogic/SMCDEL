
module Main (main) where
import Control.Monad (when)
import Data.Time (diffUTCTime,getCurrentTime,NominalDiffTime)
import System.Environment (getArgs)
import System.IO (hSetBuffering,BufferMode(NoBuffering),stdout)
import DELLANG
import KNSCAC
import EXAMPLES (genDcKnsInit,genDcReveal)

genDcCheckForm :: Int -> Form
genDcCheckForm n = Impl (Neg (PrpF $ P 1)) $
  PubAnnounceW (Xor [genDcReveal n i | i<-[1..n] ]) $
    Disj [ K "1" (Conj [Neg $ PrpF $ P k | k <- [1..n]  ])
         , Conj [ K "1" (Disj [ PrpF $ P k | k <- [2..n] ])
                , Conj [ Neg $ K "1" (PrpF $ P k) | k <- [2..n] ] ] ]

genDcValid :: Int -> Bool
genDcValid n = validViaBdd (genDcKnsInit n) (genDcCheckForm n)

dcTimeThis :: Int -> IO NominalDiffTime
dcTimeThis n = do
  start <- getCurrentTime
  let mykns@(KnS props _ _) = genDcKnsInit n
  putStr $ show (length props) ++ "\t"
  putStr $ show (length $ show mykns) ++ "\t"
  putStr $ show (length $ show $ genDcCheckForm n) ++ "\t"
  if genDcValid n then do
    end <- getCurrentTime
    return (end `diffUTCTime` start)
  else
    error "Wrong result."

mainLoop :: [Int] -> Int -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n:ns) limit = do
  putStr $ show n ++ "\t"
  result <- dcTimeThis n
  print result
  when (result <= fromIntegral limit) $ mainLoop ns limit

main :: IO ()
main = do
  args <- getArgs
  hSetBuffering stdout NoBuffering
  case args of
    [aInteger] | [(n,_)] <- reads aInteger -> do
      putStrLn $ "n" ++ "\tn(prps)"++ "\tsz(KNS)"++ "\tsz(frm)" ++ "\ttime"
      mainLoop (3:(5 : map (10*) [1..])) n
    _ -> error "Please give a maximum runtime as an argument."
