{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where


import SMCDEL.Language
    ( Prp(P),
      Form(PrpF, PubAnnounceW, Xor, Impl, Disj, Conj, Neg, K, Top),
      pubAnnounceWhetherStack )
import SMCDEL.Symbolic.S5 (validViaBdd)
import SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import SMCDEL.Examples.DiningCrypto
import qualified SMCDEL.Examples.DiningCrypto.General as DC_Gen
import Debug.Trace ( trace )
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (DdCtx, Dd, B, Z, F1, F0, S1, S0)
import SMCDEL.Examples.DiningCrypto


benchDcCheckForm :: Int -> Form
benchDcCheckForm n =
  -- PubAnnounceW (Xor [genDcReveal n i | i<-[1..n] ]) $
  -- faster but requires a fair central authority on announcing the XOR of the shared bits
  pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $ -- slow!
    Impl (Neg (PrpF $ P 1)) $
      Disj [ K "1" (Conj [Neg $ PrpF $ P k | k <- [1..n]  ])
           , Conj [ K "1" (Disj [ PrpF $ P k | k <- [2..n] ])
                  , Conj [ Neg $ K "1" (PrpF $ P k) | k <- [2..n] ] ] ]


genDcSizeCudd :: forall a b c . DdCtx a b c => Int -> Int -> IO [Int]
genDcSizeCudd n m = do
  startKns@(S5_CUDD.KnS mgr _ _ _) <- DC_Gen.genDcKnsInitCudd @a @b @c n m
  return $ loop 0 startKns (S5_CUDD.boolDdOf mgr Top) -- final check: S5_CUDD.validViaDd startKns (genDcCheckForm n)
  where
  loop i startKns@(S5_CUDD.KnS mgr _ lawb _) current_law
    | i == 0 = MyHaskCUDD.size mgr lawb : loop (i+1) startKns lawb
    | i < n  = MyHaskCUDD.size mgr (MyHaskCUDD.con mgr current_law updateDc) : loop (i+1) startKns (MyHaskCUDD.con mgr current_law updateDc)
    | i == n = []
    | otherwise = error "something went wrong with loop"
    where
      updateDc = S5_CUDD.ddOf startKns (genDcReveal n i)


benchDcValid :: Int -> Bool
benchDcValid n = validViaBdd (genDcKnsInit n) (benchDcCheckForm n)

gatherSizeData :: [Int] -> [Int] -> IO ()
gatherSizeData n m = do
  writeFile "size_data_dc.txt" "Data dining cryptographers \n\n"
  writeFile "test.txt" "Dining cryptographers \n\n"
  let cases =
        [ (i, j) | i <- n -- n many dining cryptographers
                 , j <- m -- of which m are payers
                 , j <= i -- cannot have more payers than n
                 ]
  mapM_ (uncurry writeData) cases
  where
    writeData i j = do
      -- resultb <- muddySizeCAC @B @F1 @S1 i j
      resultbc <- genDcSizeCudd @B @F1 @S1 i j
      resultf1s1 <- genDcSizeCudd @Z @F1 @S1 i j
      resultf1s0 <- genDcSizeCudd @Z @F1 @S0 i j
      resultf0s1 <- genDcSizeCudd @Z @F0 @S1 i j
      resultf0s0 <- genDcSizeCudd @Z @F0 @S0 i j
      mapM write [("BDD-complement", resultbc),("ZF1S1", resultf1s1),("ZF1S0", resultf1s0),("ZF0S1", resultf0s1),("ZF0S0", resultf0s0)]
      appendFile "size_data_dc.txt" "\n"
      where
        write (name, result) = appendFile "size_data_dc.txt" (name ++ ", m: " ++ show j ++ ", n: " ++ show i ++ ", size: " ++ show result ++ "\n")


main :: IO ()
main = do
  gatherSizeData [3] [1]


debug :: c -> String -> c
debug = flip trace
