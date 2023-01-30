{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List
import System.IO

import SMCDEL.Examples.SumAndProduct.General
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (B, Z, O1, O0, I1, I0, DdCtx)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData [60] -- TODO: getArgs

genSapSizesCac :: Int -> [Int]
genSapSizesCac n = map (\(S5_CAC.KnS _ lawb _) -> S5_CAC.size lawb) $
  updateSequence (genSapKnStruct n) [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

genSapSizesCudd ::  forall a b c . DdCtx a b c => Int -> IO [Int]
genSapSizesCudd n = do
  start <- genSapKnStructCudd @a @b @c n -- also creates manager!
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr lawb) $
    updateSequence start  [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

gatherSizeData :: [Int] -> IO ()
gatherSizeData ns = do
  putStrLn $ "Running SAP benchmark for ns=" ++ show ns ++ " and writing results to sap.dat ..."
  writeFile "sap.dat" $ "Note that these results are formulated/grouped by their elimination rule labels, and not their Input/Output complement labels as we use in our program. The labels used in our program translate to their elimination rule equivalence as follows: B O1 I1 -> EQ (nodes with equal children are eliminated), Z O1 I1 -> T0 (nodes with THEN edges pointing towards 0 leaf node are removed), Z O1 I0 -> E0, Z O0 I1 -> T1, Z O1 I0 -> E1.\n\n" ++ firstLine ++ "\n"
  mapM_ linesFor ns
  putStrLn "Done."
  where
    firstLine = intercalate "\t" $ ["n","round"] ++ map fst variants
    variants =
      [ ("BDD", return . genSapSizesCac)
      , ("BDDc",  genSapSizesCudd @B @O1 @I1)
      , ("ZO1I1", genSapSizesCudd @Z @O1 @I1)
      , ("ZO1I0", genSapSizesCudd @Z @O1 @I0)
      , ("ZO0I1", genSapSizesCudd @Z @O0 @I1)
      , ("ZO0I0", genSapSizesCudd @Z @O0 @I0)
      ]
    linesFor n = do
      putStrLn $ "Running for n = " ++ show n
      results <- mapM (($ n) . snd) variants
      appendFile "sap.dat" $ unlines [ intercalate "\t" (show n : show k : map (\xs -> show (xs !! k)) results)
                                     | k <- [0..3] ]
