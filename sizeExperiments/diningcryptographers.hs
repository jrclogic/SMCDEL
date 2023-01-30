{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List
import System.IO

import SMCDEL.Language
import SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import SMCDEL.Examples.DiningCrypto
import qualified SMCDEL.Examples.DiningCrypto.General as DC_Gen
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData [3,5,7,9,11,13] [1,3,5,7,9,11,13] -- TODO: getArgs

genDcSizeCudd :: forall a b c . DdCtx a b c => Int -> Int -> IO [Int]
genDcSizeCudd n m = do
  startKns <- DC_Gen.genDcKnsInitCudd @a @b @c n m
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr lawb) $
    updateSequence startKns [ genDcReveal n i | i <- [1..(n-1)] ]

gatherSizeData :: [Int] -> [Int] -> IO ()
gatherSizeData ns ms = do
  putStrLn $ "Running DC benchmark for ns=" ++ show ns ++ " and ms=" ++ show ms ++ " and writing results to dining.dat ..."
  writeFile "dining.dat" $ firstLine ++ "\n"
  mapM_ linesFor cases
  putStrLn "Done."
  where
    cases = [ (n, m) | n <- ns -- n many dining cryptographers
                     , m <- ms -- of which m are payers
                     , m <= n -- cannot have more payers than n
                     ]
    firstLine = intercalate "\t" $ ["n","m","round"] ++ map fst variants
    variants =
      -- Note: No CacBdd "BDD" here.
      [ ("BDDc",  genDcSizeCudd @B @F1 @S1)
      , ("ZF1S1", genDcSizeCudd @Z @F1 @S1)
      , ("ZF1S0", genDcSizeCudd @Z @F1 @S0)
      , ("ZF0S1", genDcSizeCudd @Z @F0 @S1)
      , ("ZF0S0", genDcSizeCudd @Z @F0 @S0)
      ]
    linesFor (n,m) = do
      putStrLn $ "Running for (n,m) = " ++ show (n,m)
      results <- mapM ((\f -> f n m) . snd) variants
      appendFile "dining.dat" $ unlines [ intercalate "\t" (show n : show m : show k : map (\xs -> show (xs !! k)) results)
                                        | k <- [0..(length (head results) - 1)] ]
