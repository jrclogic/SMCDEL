
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Examples.RussianCards where

import Control.Monad (replicateM)
import Data.List (delete,intersect,nub,sort)

import SMCDEL.Language
import SMCDEL.Symbolic.S5

rcPlayers :: [Agent]
rcPlayers = [alice,bob,carol]

rcNumOf :: Agent -> Int
rcNumOf "Alice" = 0
rcNumOf "Bob"   = 1
rcNumOf "Carol" = 2
rcNumOf _ = error "Unknown Agent"

rcCards :: [Int]
rcCards   = [0..6]

rcProps :: [Prp]
rcProps   = [ P k | k <-[0..((length rcPlayers * length rcCards)-1)] ]

hasCard :: Agent -> Int -> Form
hasCard i n = PrpF (P (3 * n + rcNumOf i))

-- use this in ppFormWith
rcExplain :: Prp -> String
rcExplain (P k) = show (rcPlayers !! i) ++ " `hasCard` " ++ show n where (n,i) = divMod k 3

allCardsGiven, allCardsUnique :: Form
allCardsGiven  = Conj [ Disj [ i `hasCard` n | i <- rcPlayers ] | n <- rcCards ]
allCardsUnique = Conj [ Neg $ isDouble n | n <- rcCards ] where
  isDouble n = Disj [ Conj [ x `hasCard` n, y `hasCard` n ] | x <- rcPlayers, y <- rcPlayers, x < y ]

distribute331 :: Form
distribute331 = Conj [ aliceAtLeastThree, bobAtLeastThree, carolAtLeastOne ] where
  aliceAtLeastThree = Disj [ Conj (map (alice `hasCard`) [x, y, z]) | x<-rcCards, y<-rcCards, z<-rcCards, x/=y, x/=z, y/=z  ]
  bobAtLeastThree = Disj [ Conj (map (bob `hasCard`) [x, y, z]) | x<-rcCards, y<-rcCards, z<-rcCards, x/=y, x/=z, y/=z  ]
  carolAtLeastOne = Disj [ carol `hasCard` k | k<-[0..6] ]

rusSCN :: KnowScene
rusKNS :: KnowStruct
rusSCN@(rusKNS,_) = (KnS rcProps law [ (i, obs i) | i <- rcPlayers ], defaultDeal) where
  law = boolBddOf $ Conj [ allCardsGiven, allCardsUnique, distribute331 ]
  obs i = [ P (3 * k + rcNumOf i) | k<-[0..6] ]
  defaultDeal = [P 0,P 3,P 6,P 10,P 13,P 16,P 20]

aAnnounce :: Form
aAnnounce = K alice $ Disj [ Conj (map (alice `hasCard`) hand) |
  hand <- [ [0,1,2], [0,3,4], [0,5,6], [1,3,5], [2,4,6] ] ]

bAnnounce :: Form
bAnnounce = K bob (carol `hasCard` 6)

aKnowsBs, bKnowsAs, cIgnorant :: Form
aKnowsBs = Conj [ alice `Kw` (bob `hasCard` k) | k<-rcCards ]
bKnowsAs = Conj [ bob `Kw` (alice `hasCard` k) | k<-rcCards ]
cIgnorant = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i<-rcCards ]

rcCheck :: Int -> Form
rcCheck 0 = aAnnounce

rcCheck 1 = PubAnnounce aAnnounce bKnowsAs
rcCheck 2 = PubAnnounce aAnnounce (Ck [alice,bob] bKnowsAs)

rcCheck 3 = PubAnnounce aAnnounce (K bob (PrpF (P 20)))

rcCheck 4 = PubAnnounce aAnnounce (Ck [alice,bob,carol] cIgnorant)

rcCheck 5 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [alice,bob] aKnowsBs))
rcCheck 6 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [alice,bob] bKnowsAs))
rcCheck _ = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck rcPlayers cIgnorant))

rcAllChecks :: Bool
rcAllChecks = evalViaBdd rusSCN (Conj (map rcCheck [0..7]))

checkSet :: [[Int]] -> Bool
checkSet set = all (evalViaBdd rusSCN) fs where
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` 6)
  fs = [ aliceSays
       , PubAnnounce aliceSays bKnowsAs
       , PubAnnounce aliceSays (Ck [alice,bob] bKnowsAs)
       , PubAnnounce aliceSays (Ck [alice,bob,carol] cIgnorant)
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck [alice,bob] $ Conj [aKnowsBs, bKnowsAs]))
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck rcPlayers cIgnorant)) ]

possibleHands :: [[Int]]
possibleHands = [ [x,y,z] | x <- rcCards, y <- rcCards, z <-rcCards, x < y, y < z ]

pickHands :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHands _ 0 = [ [ [ ] ] ]
pickHands unused 1 = [ [h] | h <- unused ]
pickHands unused n = concat [ [ h:hs | hs <- pickHands (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> length (h `intersect` xs) < 2 && h < xs)

allHandLists :: [ [ [Int] ] ]
allHandLists = concatMap (pickHands possibleHands) [5,6,7]

pickHandsNaive :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHandsNaive _ 0 = [ [ [ ] ] ]
pickHandsNaive unused 1 = [ [h] | h <- unused ]
pickHandsNaive unused n = concat [ [ h:hs | hs <- pickHandsNaive (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> h < xs)

alicesActions :: [[[Int]]]
alicesActions = pickHandsNaive (delete [0,1,2] possibleHands) 4

alicesForms :: [Form]
alicesForms = map translate alicesActions

translate :: [[Int]] -> Form
translate set = Disj [ Conj $ map (alice `hasCard`) h | h <- [0,1,2]:set ]

bobsForms :: [Form]
bobsForms = [carol `hasCard` n | n <- reverse [0..6]] -- FIXME relax!

allPlans :: [(Form,Form)]
allPlans = [ (a,b) | a <- alicesForms, b <- bobsForms ]

testPlan :: (Form,Form) -> Bool
testPlan (aSays,bSays) = all (evalViaBdd rusSCN) fs where
  fs = [ aSays
       , PubAnnounce aSays bKnowsAs
       , PubAnnounce aSays (Ck [alice,bob] bKnowsAs)
       , PubAnnounce aSays (Ck [alice,bob,carol] cIgnorant)
       , PubAnnounce aSays bSays
       , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob] $ Conj [aKnowsBs, bKnowsAs]))
       , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob,carol] cIgnorant)) ]

rcSolutions :: [(Form, Form)]
rcSolutions = filter testPlan allPlans

type OfflinePlan = [(Form,Form)] -- list of (announcement,goal) tuples

class Plan a where
  succeeds :: a -> Form

instance Plan OfflinePlan where
  succeeds [] = Top
  succeeds ((step,goal):rest) =
    Conj [step, PubAnnounce step goal, PubAnnounce step (succeeds rest)]

succeedsOn :: Plan a => a -> KnowScene -> Bool
succeedsOn plan scn = evalViaBdd scn (succeeds plan)

data OnlinePlan = Stop | DoAnnounce Form OnlinePlan | IfThenElse Form OnlinePlan OnlinePlan

instance Plan OnlinePlan where
  succeeds Stop = Top
  succeeds (DoAnnounce step next) = Conj [step, PubAnnounce step (succeeds next)]
  succeeds (IfThenElse check planA planB) =
    Conj [ check `Impl` succeeds planA, Neg check `Impl` succeeds planB ]

type RusCardProblem = (Int,Int,Int)

distribute :: RusCardProblem -> Form
distribute (na,nb,nc) = Conj [ alice `hasAtLeast` na, bob `hasAtLeast` nb, carol `hasAtLeast` nc ] where
  n = na + nb + nc
  hasAtLeast :: Agent -> Int -> Form
  hasAtLeast _ 0 = Top
  hasAtLeast i 1 = Disj [ i `hasCard` k | k <- nCards n ]
  hasAtLeast i 2 = Disj [ Conj (map (i `hasCard`) [x, y]) | x <- nCards n, y <- nCards n, x/=y ]
  hasAtLeast i 3 = Disj [ Conj (map (i `hasCard`) [x, y, z]) | x<-nCards n, y<-nCards n, z<-nCards n, x/=y, x/=z, y/=z ]
  hasAtLeast i k = Disj [ Conj (map (i `hasCard`) set) | set <- sets ] where
    sets = filter alldiff $ nub $ map sort $ replicateM k (nCards n) where
      alldiff [] = True
      alldiff (x:xs) = x `notElem` xs && alldiff xs

nCards :: Int -> [Int]
nCards n = [0..(n-1)]

nCardsGiven, nCardsUnique :: Int -> Form
nCardsGiven  n = Conj [ Disj [ i `hasCard` k | i <- rcPlayers ] | k <- nCards n ]
nCardsUnique n = Conj [ Neg $ isDouble k | k <- nCards n ] where
  isDouble k = Disj [ Conj [ x `hasCard` k, y `hasCard` k ] | x <- rcPlayers, y <- rcPlayers, x/=y, x < y ]

rusSCNfor :: RusCardProblem -> KnowScene
rusSCNfor (na,nb,nc) = (KnS props law [ (i, obs i) | i <- rcPlayers ], defaultDeal) where
  n = na + nb + nc
  props   = [ P k | k <-[0..((length rcPlayers * n)-1)] ]
  law = boolBddOf $ Conj [ nCardsGiven n, nCardsUnique n, distribute (na,nb,nc)  ]
  obs i = [ P (3 * k + rcNumOf i) | k<-[0..6] ]
  defaultDeal =  [ let (PrpF p) = i `hasCard` k in p | i <- rcPlayers, k <- cardsFor i ]
  cardsFor "Alice" = [0..(na-1)]
  cardsFor "Bob"   = [na..(na+nb-1)]
  cardsFor "Carol" = [(na+nb)..(na+nb+nc-1)]
  cardsFor _       = error "Who is that?"

-- the plan for (3,3,1)
basicPlan :: OfflinePlan
basicPlan =
  [ (aAnnounce, Conj [ bKnowsAs, Ck [alice,bob] bKnowsAs, Ck [alice,bob,carol] cIgnorant ] )
  , (bAnnounce, Conj [ aKnowsBs, Ck [alice,bob] aKnowsBs, Ck rcPlayers cIgnorant ] ) ]

possibleHandsN :: Int -> Int -> [[Int]]
possibleHandsN n na = filter alldiff $ nub $ map sort $ replicateM na (nCards n) where
  alldiff [] = True
  alldiff (x:xs) = x `notElem` xs && alldiff xs

allHandListsN :: Int -> Int -> [ [ [Int] ] ]
allHandListsN n na = concatMap (pickHands (possibleHandsN n na)) [5,6,7] -- FIXME how to adapt the number of hands for larger n?

aKnowsBsN, bKnowsAsN, cIgnorantN :: Int -> Form
aKnowsBsN n = Conj [ alice `Kw` (bob `hasCard` k) | k <- nCards n ]
bKnowsAsN n = Conj [ bob `Kw` (alice `hasCard` k) | k <- nCards n ]
cIgnorantN n = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i <- nCards n ]

checkSetFor :: RusCardProblem -> [[Int]] -> Bool
checkSetFor (na,nb,nc) set = plan `succeedsOn` rusSCNfor (na,nb,nc) where
  n = na + nb + nc
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` last (nCards n))
  plan =
   [ (aliceSays, Conj [ bKnowsAsN n, Ck [alice,bob] (bKnowsAsN n), Ck [alice,bob,carol] (cIgnorantN n) ] )
   , (bobSays  , Conj [ Ck [alice,bob] $ Conj [aKnowsBsN n, bKnowsAsN n], Ck rcPlayers (cIgnorantN n) ] )
   ]

checkHandsFor :: RusCardProblem -> [ ( [[Int]], Bool) ]
checkHandsFor (na,nb,nc) = map (\hs -> (hs, checkSetFor (na,nb,nc) hs)) (allHandListsN n na) where
  n = na + nb + nc

allCasesUpTo :: Int -> [RusCardProblem]
allCasesUpTo bound = [ (na,nb,nc) | na <- [1..bound]
                                  , nb <- [1..(bound-na)]
                                  , nc <- [1..(bound-(na+nb))]
                                  -- these restrictions are only proven
                                  -- for two announcement plans!
                                  , nc < (na - 1)
                                  , nc < nb ]
