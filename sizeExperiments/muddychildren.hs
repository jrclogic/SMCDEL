{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main where

import Data.List

import SMCDEL.Language
import SMCDEL.Examples.MuddyChildren
import System.IO.Unsafe
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (sparsity, size, Dd, B, Z, F1, F0, S1, S0, DdCtx)
import SMCDEL.Symbolic.S5_CUDD (boolDdOf)
import SMCDEL.Language (booloutofForm)
import System.Environment (getArgs)


-- general muddy children

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]

checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

genMuddyKnStructCudd :: DdCtx a b c => Int -> IO (S5_CUDD.KnowStruct a b c)
genMuddyKnStructCudd n = do
  mgr <- MyHaskCUDD.makeManagerZ n
  let law = S5_CUDD.boolDdOf mgr (father n)
  let obs = [ (show x,delete (P x) (mudPs n)) | x <- [1..n] ]
  return $ S5_CUDD.KnS mgr (mudPs n) law obs



muddySizeCUDD :: forall a b c . DdCtx a b c => Int -> Int -> IO [Int]
muddySizeCUDD n m = do
  start@(S5_CUDD.KnS mgr _ _ _) <- (genMuddyKnStructCudd @a @b @c n) -- also creates the manager!
  return (loop 0 start)  where
    loop i kns

      | i == 0 = info kns : loop (i+1) kns
      | i < m = info (kns `update` nobodyknows n) : loop (i+1) (kns `update` nobodyknows n)
      | i == m = [] -- final check possible here.
      | otherwise = error ("something went wrong with loop: " ++ show i) where

        finalcheck (S5_CUDD.KnS mgr _ lawb _) = show b  where
          list = [ (x, x<=m) | x<-[1..n]]
          b  = MyHaskCUDD.restrictSet mgr lawb list == MyHaskCUDD.top mgr

        info (S5_CUDD.KnS mgr _ law _) = MyHaskCUDD.size mgr law


muddySizeCAC :: Int -> Int -> [Int]
muddySizeCAC n m = loop 0 cuddMudScnInit  where
  cuddMudScnInit = S5_CAC.KnS (mudPs n) (S5_CAC.boolBddOf (father n)) [ (show x,delete (P x) (mudPs n)) | x <- [1..n] ]
  loop i kns
    | i == 0 = info kns : loop (i+1) kns
    | i < m = info (kns `unsafeUpdate` nobodyknows n) : loop (i+1) (kns `unsafeUpdate` nobodyknows n)
    | i == m = []
    | otherwise = error ("something went wrong with loop: " ++ show i) where

      info (S5_CAC.KnS _ lawb _) = S5_CAC.size lawb



gatherSizeData :: [Int] -> [Int] -> IO ()
gatherSizeData n m = do
  writeFile "size_data_muddy.txt" "Data muddy children \n\n"
  writeFile "test.txt" "Muddy children \n\n"
  let cases =
        [ (i, j) | i <- n -- n many children
                 , j <- m -- of which m are muddy
                 , j <= i -- cannot have more muddy than n
                 ]
  mapM_ (uncurry writeData) cases
  where
    writeData i j = do
      -- let resultb = muddySizeCAC i j

      resultbc <- muddySizeCUDD @B @F1 @S1 i j
      resultf1s1 <- muddySizeCUDD @Z @F1 @S1 i j
      resultf1s0 <- muddySizeCUDD @Z @F1 @S0 i j
      resultf0s1 <- muddySizeCUDD @Z @F0 @S1 i j
      resultf0s0 <- muddySizeCUDD @Z @F0 @S0 i j
      mapM write [("BDD-complement", resultbc),("ZF1S1", resultf1s1),("ZF1S0", resultf1s0),("ZF0S1", resultf0s1),("ZF0S0", resultf0s0)]
      appendFile "size_data_muddy.txt" "\n"
      where
        write (name, result) = appendFile "size_data_muddy.txt" (name ++ ", m: " ++ show j ++ ", n: " ++ show i ++ ", size: " ++ show result ++ "\n")

main :: IO ()

main = do
  args <- getArgs
  {- (n, m) <- case args of
    [aInteger] | [(n,_)] <- reads aInteger -> return n
    _ -> do
      putStrLn "No arguments given, defaulting to single test for three children of which three are muddy."
      return ([3], [3]) -}
  gatherSizeData
    [30] --[n]
    [30] --[m]