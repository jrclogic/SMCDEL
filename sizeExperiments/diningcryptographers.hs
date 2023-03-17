{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List
import System.IO

import SMCDEL.Language
import SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import SMCDEL.Symbolic.S5 as S5
import SMCDEL.Examples.DiningCrypto
import qualified SMCDEL.Examples.DiningCrypto.General as DC_Gen
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData [3,5,7,9,11,13] [1]

genDcSizeCudd :: forall a b c . DdCtx a b c => Int -> Int -> IO [Int]
genDcSizeCudd n m = do
  startKns <- DC_Gen.genDcKnsInitCudd @a @b @c n m
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr lawb) $
    updateSequence startKns [ genDcReveal n i | i <- [1..(n-1)] ]

genDcSizeCac :: Int -> Int -> [Int]
genDcSizeCac n m = map info $ updateSequence start fs  where
  start = DC_Gen.genDcKnsInit n m
  info (S5.KnS _ lawb _) = S5.size lawb
  fs = [ genDcReveal n i | i <- [1..(n-1)] ]

gatherSizeData :: [Int] -> [Int] -> IO ()
gatherSizeData ns ms = do
  putStrLn $ "Running DC benchmark for ns=" ++ show ns ++ " and ms=" ++ show ms ++ " and writing results to dining.dat ..."
  writeFile "dining.dat" $ "# Note: round -1 indicates the average.\n" ++ firstLine ++ "\n"
  mapM_ linesFor cases
  putStrLn "Done."
  where
    cases = [ (n, m) | n <- ns -- n many dining cryptographers
                     , m <- ms -- of which m are payers
                     , m <= n -- cannot have more payers than n
                     ]
    firstLine = intercalate "\t" $ ["n","m","round"] ++ map fst variants
    variants =
      -- label result columns with elimination rules, not i/o complements:
      [ ("BDD", \ n m -> return $ genDcSizeCac n m)
      , ("BDDc",  genDcSizeCudd @B @O1 @I1)
      , ("T0", genDcSizeCudd @Z @O1 @I1)
      , ("T1", genDcSizeCudd @Z @O0 @I1)
      , ("E0", genDcSizeCudd @Z @O1 @I0)
      , ("E1", genDcSizeCudd @Z @O0 @I0)
      ]
    linesFor (n,m) = do
      putStrLn $ "Running for (n,m) = " ++ show (n,m)
      results <- mapM ((\f -> f n m) . snd) variants
      appendFile "dining.dat" $ unlines $
        [ intercalate "\t" (show n : show m : show k : map (\xs -> show (xs !! k)) results)
        | k <- [0..(length (head results) - 1)] ]
        ++
        [ intercalate "\t" (show n : show m : "-1" : map (\xs -> show (fromIntegral (sum xs) / 4 :: Double)) results) ]
