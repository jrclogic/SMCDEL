{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main where

import Data.List
import System.IO

import SMCDEL.Language
import SMCDEL.Examples.MuddyChildren
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData
    [5,10,15,20,25,30,35,40] -- n: number of children
    [5,10,15,20,25,30,35,40] -- m: number of muddy children

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

genMuddyKnStructCudd :: DdCtx a b c => Int -> IO (S5_CUDD.KnowStruct a b c)
genMuddyKnStructCudd n = do
  mgr <- MyHaskCUDD.makeManagerZ n
  let law = S5_CUDD.boolDdOf mgr (father n)
  let obs = [ (show x,delete (P x) (mudPs n)) | x <- [1..n] ]
  return $ S5_CUDD.KnS mgr (mudPs n) law obs

muddySizeCUDD :: forall a b c . DdCtx a b c => Int -> Int -> IO [Int]
muddySizeCUDD n m = do
  start <- genMuddyKnStructCudd @a @b @c n -- also creates the manager!
  return $ map info $ updateSequence start fs where
    info (S5_CUDD.KnS mgr _ law _) = MyHaskCUDD.size mgr law
    fs = replicate (m-1) (nobodyknows n)

muddySizeCAC :: Int -> Int -> [Int]
muddySizeCAC n m = map info $ updateSequence start fs  where
  start = S5_CAC.KnS (mudPs n)
                     (S5_CAC.boolBddOf (father n))
                     [ (show x,delete (P x) (mudPs n)) | x <- [1..n] ]
  info (S5_CAC.KnS _ lawb _) = S5_CAC.size lawb
  fs = replicate (m-1) (nobodyknows n)

gatherSizeData :: [Int] -> [Int] -> IO ()
gatherSizeData ns ms = do
  putStrLn $ "Running MC benchmark for ns=" ++ show ns ++ " and ms=" ++ show ms ++ " and writing results to mc.dat ..."
  writeFile "mc.dat" $ "# Note: round -1 indicates the average.\n" ++ firstLine ++ "\n"
  mapM_ linesFor cases
  where
    cases = [ (n, m) | n <- ns -- n many children
                     , m <- ms -- of which m are muddy
                     , m <= n  -- cannot have more muddy than n
                     ]
    firstLine = intercalate "\t" $ ["n","m","round"] ++ map fst variants
    variants =
      -- label result columns with elimination rules, not i/o complements:
      [ ("BDD", \n m -> return $ muddySizeCAC n m)
      , ("BDDc",  muddySizeCUDD @B @O1 @I1)
      , ("T0", muddySizeCUDD @Z @O1 @I1)
      , ("T1", muddySizeCUDD @Z @O0 @I1)
      , ("E0", muddySizeCUDD @Z @O1 @I0)
      , ("E1", muddySizeCUDD @Z @O0 @I0)
      ]
    linesFor (n,m) = do
      putStrLn $ "Running for (n,m) = " ++ show (n,m)
      results <- mapM ((\f -> f n m) . snd) variants
      appendFile "mc.dat" $ unlines $
        [ intercalate "\t" (show n : show m : show k : map (\xs -> show (xs !! k)) results)
        | k <- [0..(m-1)] ]
        ++
        [ intercalate "\t" (show n : show m : "-1" : map (\xs -> show (fromIntegral (sum xs) / 4 :: Double)) results) ]
