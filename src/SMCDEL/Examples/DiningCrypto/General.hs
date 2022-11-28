module SMCDEL.Examples.DiningCrypto.General where

import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD (makeManagerZ, Manager)
import Data.List
import qualified Data.HasCacBDD as S5_CAC

dcScnInit :: Int -> (Bool,Bool,Bool) -> S5_CAC.KnowScene
dcScnInit payer (b1,b2,b3) = ( S5_CAC.KnS props law obs , truths ) where
  props = [ P 0   -- The NSA paid
          , P 1   -- Alice paid
          , P 2   -- Bob paid
          , P 3   -- Charlie paid
          , P 4   -- shared bit of Alice and Bob
          , P 5   -- shared bit of Alice and Charlie
          , P 6 ] -- shared bit of Bob and Charlie
  law   = S5_CAC.boolBddOf $ Conj [ someonepaid, notwopaid ]
  obs   = [ (show (1::Int),[P 1, P 4, P 5])
          , (show (2::Int),[P 2, P 4, P 6])
          , (show (3::Int),[P 3, P 5, P 6]) ]
  truths = [ P payer ] ++ [ P 4 | b1 ] ++ [ P 5 | b2 ] ++ [ P 6 | b3 ]

dcScn1 :: S5_CAC.KnowScene
dcScn1 = dcScnInit 1 (True,True,False)

someonepaid, notwopaid :: Form
someonepaid = Disj (map (PrpF . P) [0..3])
notwopaid = Conj [ Neg $ Conj [ PrpF $ P x, PrpF $ P y ] | x<-[0..3], y<-[(x+1)..3] ]

reveal :: Int -> Form
reveal 1 = Xor (map PrpF [P 1, P 4, P 5])
reveal 2 = Xor (map PrpF [P 2, P 4, P 6])
reveal _ = Xor (map PrpF [P 3, P 5, P 6])

dcScn2 :: S5_CAC.KnowScene
dcScn2 = update dcScn1 (Conj [reveal 1, reveal 2, reveal 3])

everyoneKnowsWhetherNSApaid :: Form
everyoneKnowsWhetherNSApaid = Conj [ Kw (show i) (PrpF $ P 0) | i <- [1..3]::[Int] ]

nobodyknowsWhoPaid :: Form
nobodyknowsWhoPaid = Conj
  [ Impl (PrpF (P 1)) (Conj [Neg $ K "2" (PrpF $ P 1), Neg $ K "3" (PrpF $ P 1) ])
  , Impl (PrpF (P 2)) (Conj [Neg $ K "1" (PrpF $ P 2), Neg $ K "3" (PrpF $ P 2) ])
  , Impl (PrpF (P 3)) (Conj [Neg $ K "1" (PrpF $ P 3), Neg $ K "2" (PrpF $ P 3) ]) ]

dcCheckForm :: Form
dcCheckForm = PubAnnounceW (reveal 1) $ PubAnnounceW (reveal 2) $ PubAnnounceW (reveal 3) $
    Conj [ everyoneKnowsWhetherNSApaid, nobodyknowsWhoPaid ]

dcValid :: Bool
dcValid = S5_CAC.validViaBdd dcStruct dcCheckForm where (dcStruct,_) = dcScn1


-- * Generalised Dining Cryptographers (with n diners and m payers)

-- Creates a disjoint form where each term has n propositions in conjunction of which m are positive and n-m are negative.
-- All terms add up to all possible combinations of n choose m, giving a general XOR where m propositions have to be positive.
genXorM :: Int -> Int -> Form
genXorM n m = Disj
  [ Conj
    ([PrpF (P p) | p <- x]
      ++ [Neg (PrpF (P i)) | i <- y])
  | x <- select
  , let y = [0 .. n] \\ x
  ]
  where
    select = combinations m [0 .. n]

combinations :: Int -> [a] -> [[a]]
combinations k ns = filter ((k==).length) $ subsequences ns

genDcEveryoneKnowsWhetherNSApaid :: Int -> Form
genDcEveryoneKnowsWhetherNSApaid n = Conj [ Kw (show i) (PrpF $ P 0) | i <- [1..n] ]

-- XOR between shared secret bits for agent i
genDcReveal :: Int -> Int -> Int -> Form
genDcReveal n m i = Xor (map PrpF ps) where
  (S5_CAC.KnS _ _ obs) = genDcKnsInit n m
  (Just ps)     = lookup (show i) obs

genDcNobodyknowsWhoPaid :: Int -> Form
genDcNobodyknowsWhoPaid n =
  Conj [ Impl (PrpF (P i)) (Conj [Neg $ K (show k) (PrpF $ P i) | k <- delete i [1..n] ]) | i <- [1..n] ]

genDcCheckForm :: Int -> Int -> Form
genDcCheckForm n m =
  pubAnnounceWhetherStack [ genDcReveal n m i | i<-[1..n] ] $
    Conj [ genDcEveryoneKnowsWhetherNSApaid n, genDcNobodyknowsWhoPaid n ]

genDcConclusion :: Int -> Form
genDcConclusion n =
    Conj [ genDcEveryoneKnowsWhetherNSApaid n, genDcNobodyknowsWhoPaid n ]

genDcValid :: Int -> Int -> Bool
genDcValid n m = S5_CAC.validViaBdd (genDcKnsInit n m) (genDcCheckForm n m)

dcProtocolCac :: Int -> Int -> S5_CAC.Bdd
dcProtocolCac n m = S5_CAC.bddOf (genDcKnsInit n m) (Conj [ genDcEveryoneKnowsWhetherNSApaid n, genDcNobodyknowsWhoPaid n ])

-- | Initial knowledge structure for General Dining Cryptographers with a complete graph.
genDcKnsInit :: Int -> Int -> S5_CAC.KnowStruct
genDcKnsInit n m = S5_CAC.KnS props law obs where
  props = [ P 0 ] -- The NSA paid
    ++ [ (P 1) .. (P n) ] -- agent i paid
    ++ sharedbits
  law = S5_CAC.boolBddOf $ genXorM n m
  obs = [ (show i, obsfor i) | i<-[1..n] ]
  sharedbitLabels = [ [k,l] | k <- [1..n], l <- [1..n], k<l ] -- n(n-1)/2 shared bits
  sharedbitRel = zip sharedbitLabels [ (P $ n+1) .. ]
  sharedbits =  map snd sharedbitRel
  obsfor i =  P i : map snd (filter (\(label,_) -> i `elem` label) sharedbitRel)

dcProtocolCudd :: MyHaskCUDD.DdCtx a b c => Int -> Int -> IO (MyHaskCUDD.Dd a b c)
dcProtocolCudd n m = do
  startKns <- genDcKnsInitCudd n m
  return $ S5_CUDD.ddOf startKns (Conj [ genDcEveryoneKnowsWhetherNSApaid n, genDcNobodyknowsWhoPaid n ])

genDcKnsInitCudd :: MyHaskCUDD.DdCtx a b c => Int -> Int -> IO (S5_CUDD.KnowStruct a b c)
genDcKnsInitCudd n m = makeManagerZ (maximum (map fromEnum props)) >>= \mgr -> do
  let law = S5_CUDD.boolDdOf mgr $ genXorM n m
  return $ S5_CUDD.KnS mgr props law obs
  where
    sharedbitLabels = [ [k,l] | k <- [1..n], l <- [1..n], k<l ] -- n(n-1)/2 shared bits
    sharedbitRel = zip sharedbitLabels [ (P $ n+1) .. ]
    sharedbits =  map snd sharedbitRel
    props = [ P 0 ] -- The NSA paid
          ++ [ (P 1) .. (P n) ] -- agent i paid
          ++ sharedbits
    obsfor i =  P i : map snd (filter (\(label,_) -> i `elem` label) sharedbitRel)
    obs = [ (show i, obsfor i) | i<-[1..n] ]



mgrOf :: S5_CUDD.KnowStruct a b c -> Manager
mgrOf (S5_CUDD.KnS m _ _ _) = m
