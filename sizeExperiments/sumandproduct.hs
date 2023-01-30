{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List
import System.IO

import SMCDEL.Examples.SumAndProduct.General
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData [60,63,64,65,120] -- TODO: getArgs

genSapSizesCac :: Int -> [Int]
genSapSizesCac n = map (\(S5_CAC.KnS _ lawb _) -> S5_CAC.size lawb) $
  updateSequence (genSapKnStruct n) [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

genSapSizesCudd :: forall a b c . DdCtx a b c => Int -> IO [Int]
genSapSizesCudd n = do
  start <- genSapKnStructCudd @a @b @c n -- also creates manager!
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr lawb) $
    updateSequence start  [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

genSapSizesCuddViaConvert :: forall b c . (Convert b c) => Int -> IO [Int]
genSapSizesCuddViaConvert n = do
  start <- genSapKnStructCudd @B @O1 @I1 n -- also creates manager!
  let context = map fromEnum $ vocabOf start
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr (convertToZDD mgr context lawb :: Dd Z b c)) $
    updateSequence start  [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

gatherSizeData :: [Int] -> IO ()
gatherSizeData ns = do
  putStrLn $ "Running SAP benchmark for ns=" ++ show ns ++ " and writing results to sap.dat ..."
  writeFile "sap.dat" $
    unlines [ "# Note: result columns are labelled with elimination"
            , "# rules, not the input/output complement labels."
            , "# The labels translate as follows:"
            , "#   B O1 I1 -> EQ (nodes with equal children are eliminated)"
            , "#   Z O1 I1 -> T0 (nodes with THEN edges to 0 leaf are removed)"
            , "#   Z O1 I0 -> E0"
            , "#   Z O0 I1 -> T1"
            , "#   Z O1 I0 -> E1."
            ] ++ firstLine ++ "\n"
  mapM_ linesFor ns
  putStrLn "Done."
  where
    firstLine = intercalate "\t" $ ["n","round"] ++ map fst variants
    variants =
      [ ("BDD", return . genSapSizesCac)
      , ("BDDc",  genSapSizesCudd @B @O1 @I1)
      -- via conversion, fast:
      , ("ZO1I1", genSapSizesCuddViaConvert @O1 @I1)
      , ("ZO1I0", genSapSizesCuddViaConvert @O1 @I0)
      , ("ZO0I1", genSapSizesCuddViaConvert @O0 @I1)
      , ("ZO0I0", genSapSizesCuddViaConvert @O0 @I0)
      -- directly on ZDDs, slow:
      -- , ("ZO1I1", genSapSizesCudd @Z @O1 @I1)
      -- , ("ZO1I0", genSapSizesCudd @Z @O1 @I0)
      -- , ("ZO0I1", genSapSizesCudd @Z @O0 @I1)
      -- , ("ZO0I0", genSapSizesCudd @Z @O0 @I0)
      ]
    linesFor n = do
      putStrLn $ "Running for n = " ++ show n
      results <- mapM (($ n) . snd) variants
      appendFile "sap.dat" $ unlines [ intercalate "\t" (show n : show k : map (\xs -> show (xs !! k)) results)
                                     | k <- [0..3] ]
