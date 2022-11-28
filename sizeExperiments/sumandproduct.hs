{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where
import System.Environment (getArgs)
import SMCDEL.Examples.SumAndProduct.General
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (B, Z, F1, F0, S1, S0, DdCtx)

main :: IO ()
main = do
  gatherSizeData [ 64]

infoCudd :: S5_CUDD.KnowStruct a b c -> Int
infoCudd (S5_CUDD.KnS mgr _ lawb _) = MyHaskCUDD.size mgr lawb

genSapWhereWithSizeCac :: Int -> [Int]
genSapWhereWithSizeCac n = getSizePerUpdate where
  info (S5_CAC.KnS _ lawb _) = S5_CAC.size lawb
  getSizePerUpdate = map info
    [ genSapKnStruct n
    , genSapKnStruct n `update` genSapForm1 n
    , genSapKnStruct n `update` genSapForm1 n `update` genSapForm2 n
    , genSapKnStruct n `update` genSapForm1 n `update` genSapForm2 n `update` genSapForm3 n ]


genSapWhereWithSizeCudd ::  forall a b c . DdCtx a b c => Int -> IO [Int]
genSapWhereWithSizeCudd n = do
  start <- genSapKnStructCudd @a @b @c n -- also creates manager!
  let resultsPerUpdate = map infoCudd
        [ start
        , start `unsafeUpdate` genSapForm1 n
        , start `unsafeUpdate` genSapForm1 n `unsafeUpdate` genSapForm2 n
        , start `unsafeUpdate` genSapForm1 n `unsafeUpdate` genSapForm2 n `unsafeUpdate` genSapForm3 n]
  -- let checkAnswer = start `unsafeUpdate` genSapForm1 n `unsafeUpdate` genSapForm2 n `unsafeUpdate` genSapForm3 n
  return resultsPerUpdate

gatherSizeData :: [Int] -> IO ()
gatherSizeData ns = do
  writeFile "size_data_sap.txt" "Sum and product \n\n"
  mapM_ writeData ns
  where
    writeData i = do
      let resultb = genSapWhereWithSizeCac i
      resultbc <- genSapWhereWithSizeCudd @B @F1 @S1 i
      resultf1s1 <- genSapWhereWithSizeCudd @Z @F1 @S1 i
      resultf1s0 <- genSapWhereWithSizeCudd @Z @F1 @S0 i
      resultf0s1 <- genSapWhereWithSizeCudd @Z @F0 @S1 i
      resultf0s0 <- genSapWhereWithSizeCudd @Z @F0 @S0 i
      mapM_ write [("Bdd", resultb),("Bdd-complement", resultbc),("ZF1S1", resultf1s1),("ZF1S0", resultf1s0),("ZF0S1", resultf0s1),("ZF0S0", resultf0s0)]
      appendFile "size_data_sap.txt" "\n"
      where
        write (name, result) = appendFile "size_data_sap.txt" (name ++ ", n: " ++ show i ++ ", size: " ++ show result ++ "\n")

