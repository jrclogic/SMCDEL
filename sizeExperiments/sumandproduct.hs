{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List

import SMCDEL.Examples.SumAndProduct.General
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (B, Z, F1, F0, S1, S0, DdCtx)

main :: IO ()
main = gatherSizeData [50] -- TODO: getArgs

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
  writeFile "sap.dat" $ firstLine ++ "\n"
  mapM_ linesFor ns
  putStrLn "Done."
  where
    firstLine = intercalate "\t" $ ["n","round"] ++ map fst variants
    variants =
      [ ("BDD", return . genSapSizesCac)
      , ("BDD-c", genSapSizesCudd @B @F1 @S1)
      , ("ZF1S1", genSapSizesCudd @Z @F1 @S1)
      , ("ZF1S0", genSapSizesCudd @Z @F1 @S0)
      , ("ZF0S1", genSapSizesCudd @Z @F0 @S1)
      , ("ZF0S0", genSapSizesCudd @Z @F0 @S0)
      ]
    linesFor n = do
      putStrLn $ "Running for n = " ++ show n
      results <- mapM (($ n) . snd) variants
      appendFile "sap.dat" $ unlines [ intercalate "\t" (show n : show k : map (\xs -> show (xs !! k)) results)
                                     | k <- [0..3] ]
