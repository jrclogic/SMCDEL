{- | General Sum and Product, where the sum of x and y is up to n.
-}

module SMCDEL.Examples.SumAndProduct.General where

import Data.List
import Data.Maybe

import SMCDEL.Language
import SMCDEL.Internal.Help
import SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD

sapSolutionsCac :: Int -> [[Prp]]
sapSolutionsCac n = whereViaBdd (genSapKnStruct n) (genSapProtocol n )

sapExplainState :: Int -> [Prp] -> String
sapExplainState n truths = concat
  [ "x = ", explain (genXProps n)
  , ", y = ", explain (genYProps n)
  , ", x+y = ", explain (genSProps n)
  , " and x*y = ", explain (genPProps n) ]
  where explain = show . nmbr truths

nmbr :: [Prp] -> [Prp] -> Int
nmbr truths s = fromMaybe (error "Value not found") $
  elemIndex (s `intersect` truths) (powerset s)

-- | Knowledge structure for general Sum and Product.
-- Alice knows the sum of the two numbers, Bob knows the product.
-- The state law ensures that for each pair of x and y the s and p are correct,
-- which can be written as a disjuction of conjunction terms, consisting of x, y, s and p.
genSapKnStruct :: Int -> KnowStruct
genSapKnStruct n = KnS (genSapAllProps n) law obs where
  law = boolBddOf $ genSapLaw n
  obs = [ (alice, genSProps n), (bob, genPProps n) ]

-- from max sum to max product
maxProduct :: Int -> Int
maxProduct n = ceiling (((fromIntegral :: Int -> Double) n / 2) * ((fromIntegral :: Int -> Double) n / 2))

--from max to binary representation max
maxBinary :: Int -> Int
maxBinary = ceiling . logBase 2.0 . (fromIntegral :: Int -> Double)

-- possible pairs 1<x<y, x+y<=n
genPairs :: Int -> [(Int, Int)]
genPairs n = [(x,y) | x<-[2..n], y<-[2..n], x<y, x+y<=n]

-- e.g. 7 propositions needed to label x for s = [2..100], because 2^6 = 64 < 100 < 128 = 2^7
-- we continue for y s and p where the previous variable range stopped.
genXProps, genYProps, genSProps, genPProps :: Int -> [Prp]
genXProps n = [(P  1)..(P $ maxBinary n)]
genYProps n = [(P $ maxBinary n + 1)..(P $ maxBinary n * 2)]
genSProps n = [(P $ maxBinary n * 2 + 1)..(P $ maxBinary n * 3)]
genPProps n = [(P $ maxBinary n * 3 + 1)..(P $ maxBinary n * 3 + 1 + maxBinary (maxProduct n) )]

-- all variables needed for SAP with a given n (maximum sum)
genSapAllProps :: Int -> [Prp]
genSapAllProps n = sort $ genXProps n ++ genYProps n ++ genSProps n ++ genPProps n

-- generates only the argument (x,y,s or p) set to true while all others are false.
-- we use x-1 because !! starts counting at 0, whereas we represent boolean numbers starting from 1.
genXIs, genYIs, genSIs, genPIs :: Int -> Int -> Form
genXIs x n = booloutofForm (powerset (genXProps n) !! (x-1)) (genXProps n)
genYIs y n = booloutofForm (powerset (genYProps n) !! (y-1)) (genYProps n)
genSIs s n = booloutofForm (powerset (genSProps n) !! (s-1)) (genSProps n)
genPIs p n = booloutofForm (powerset (genPProps n) !! (p-1)) (genPProps n)

-- only x and y are possible
genxyAre :: (Int,Int) -> Int ->  Form
genxyAre (x,y) n = Conj [ genXIs x n, genYIs y n ]

genSapKnows :: Agent -> Int -> Form
genSapKnows i n = Disj [ K i (genxyAre p n) | p <- genPairs n]

-- State law for general SAP.
genSapLaw :: Int -> Form
genSapLaw n = Disj [ Conj [ genxyAre (x,y) n, genSIs (x+y) n, genPIs (x*y) n ] | (x,y) <- genPairs n ]

genSapForm1, genSapForm2, genSapForm3 :: Int -> Form
genSapForm1 n = K alice $ Neg (genSapKnows bob n) -- Sum: I knew that you didn't know the numbers.
genSapForm2 = genSapKnows bob  -- Product: Now I know the two numbers
genSapForm3 = genSapKnows alice -- Sum: Now I know the two numbers too

genSapProtocol :: Int -> Form
genSapProtocol n = Conj [ genSapForm1 n
                   , PubAnnounce (genSapForm1 n) (genSapForm2 n)
                   , PubAnnounce (genSapForm1 n) (PubAnnounce (genSapForm2 n) (genSapForm3 n)) ]

genSapKnStructCudd :: (MyHaskCUDD.DdCtx a b c) => Int -> IO (S5_CUDD.KnowStruct a b c)
genSapKnStructCudd n = do
  mgr <- MyHaskCUDD.makeManagerZ (maximum (map fromEnum (genSapAllProps n)))
  let law = S5_CUDD.boolDdOf mgr $ genSapLaw n
  let obs = [ (alice, genSProps n), (bob, genPProps n) ]
  return $ S5_CUDD.KnS mgr (genSapAllProps n) law obs
