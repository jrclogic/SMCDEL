{-# LANGUAGE FlexibleInstances #-}

module SMCDEL.Examples.RussianCards where

import Control.Monad (replicateM)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),delete,intersect,nub,sort)
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (powerset)
import SMCDEL.Language
import SMCDEL.Other.Planning
import SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.K as K

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

hasHand :: Agent -> [Int] -> Form
hasHand i ns = Conj $ map (i `hasCard`) ns

rcExplain :: Prp -> String
rcExplain (P k) = (rcPlayers !! i) ++ " has card " ++ show n where (n,i) = divMod k 3

allCardsGiven, allCardsUnique :: Form
allCardsGiven  = Conj [ Disj [ i `hasCard` n | i <- rcPlayers ] | n <- rcCards ]
allCardsUnique = Conj [ Neg $ isDouble n | n <- rcCards ] where
  isDouble n = Disj [ Conj [ x `hasCard` n, y `hasCard` n ] | x <- rcPlayers, y <- rcPlayers, x < y ]

distribute331 :: Form
distribute331 = Conj [ aliceAtLeastThree, bobAtLeastThree, carolAtLeastOne ] where
  triples = [ [x, y, z] | x <- rcCards, y <- delete x rcCards, z <- rcCards \\ [x,y] ]
  aliceAtLeastThree = Disj [ Conj (map (alice `hasCard`) t) | t <- triples ]
  bobAtLeastThree   = Disj [ Conj (map (bob   `hasCard`) t) | t <- triples ]
  carolAtLeastOne   = Disj [ carol `hasCard` k | k<-[0..6] ]

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
aKnowsBs = Conj [ alice `Kw` (bob   `hasCard` k) | k<-rcCards ]
bKnowsAs = Conj [ bob   `Kw` (alice `hasCard` k) | k<-rcCards ]
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
possibleHands = [ [x,y,z] | x <- rcCards, y <- filter (> x) rcCards, z <-filter (> y) rcCards ]

pickHandsNoCrossing :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHandsNoCrossing _ 0 = [ [ [ ] ] ]
pickHandsNoCrossing unused 1 = [ [h] | h <- unused ]
pickHandsNoCrossing unused n = concat [ [ h:hs | hs <- pickHandsNoCrossing (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> length (h `intersect` xs) < 2 && h < xs) -- do not allow intersection > 2

allHandLists, safeHandLists :: [ [ [Int] ] ]
allHandLists = concatMap (pickHandsNoCrossing possibleHands) [5,6,7]
safeHandLists = sort (filter checkSet allHandLists)

alicesActions :: [Form]
alicesActions = [ Disj $ map (alice `hasHand`) ([0,1,2]:otherHands) | otherHands <- handLists ] where
  handLists :: [ [ [Int] ] ]
  handLists = pickHands (delete [0,1,2] possibleHands) 4
  pickHands :: [ [Int] ] -> Int -> [ [ [Int] ] ]
  pickHands _     0 = [ [ [ ] ] ]
  pickHands hands 1 = [ [ h   ] | h <- hands ]
  pickHands hands n = [ h:hs    | h <- hands, hs <- pickHands (filter (h <) hands) (n-1) ]

bobsActions :: [Form]
bobsActions = [ carol `hasCard` n | n <- reverse [4..6] ]

rcSolutions :: [ [Form] ]
rcSolutions = [ [a, b] | a <- alicesActions, b <- bobsActions, testPlan a b ] where
  testPlan :: Form -> Form -> Bool
  testPlan aSays bSays = all (evalViaBdd rusSCN)
    -- NOTE: increasing checks are faster than one big conjunction!
    [ aSays
    , PubAnnounce aSays bKnowsAs
    , PubAnnounce aSays cIgnorant
    , PubAnnounce aSays bSays
    , PubAnnounce aSays (PubAnnounce bSays aKnowsBs)
    , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob] $ Conj [cIgnorant,aKnowsBs,bKnowsAs])) ]

rcPlan :: OfflinePlan
rcPlan = [ aAnnounce, bAnnounce ]

rcGoal :: Form
rcGoal = Conj [ aKnowsBs
              , bKnowsAs
              , Ck [alice,bob] (Conj [aKnowsBs, bKnowsAs])
              , Ck [alice,bob,carol] cIgnorant ]

rcSolutionsViaPlanning :: [OfflinePlan]
rcSolutionsViaPlanning = offlineSearch maxSteps start actions constraints goal where
  maxSteps    = 2 -- We need two steps!
  start       = rusSCNfor (3,3,1)
  actions     = alicesActions ++ bobsActions
  constraints = [cIgnorant,bKnowsAs]
  goal        = Conj [aKnowsBs, bKnowsAs]

type RusCardProblem = (Int,Int,Int)

distribute :: RusCardProblem -> Form
distribute (na,nb,nc) = Conj [ alice `hasAtLeast` na
                             , bob   `hasAtLeast` nb
                             , carol `hasAtLeast` nc ] where
  n = na + nb + nc
  hasAtLeast :: Agent -> Int -> Form
  hasAtLeast _ 0 = Top
  hasAtLeast i 1 = Disj [ i `hasCard` k | k <- nCards n ]
  hasAtLeast i k = Disj [ Conj (map (i `hasCard`) (sort set))
                        | set <- powerset (nCards n), length set == k ]

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

possibleHandsN :: Int -> Int -> [[Int]]
possibleHandsN n na = filter alldiff $ nub $ map sort $ replicateM na (nCards n) where
  alldiff [] = True
  alldiff (x:xs) = x `notElem` xs && alldiff xs

allHandListsN :: Int -> Int -> [ [ [Int] ] ]
allHandListsN n na = concatMap (pickHandsNoCrossing (possibleHandsN n na)) [5,6,7] -- FIXME how to adapt the number of hands for larger n?

aKnowsBsN, bKnowsAsN, cIgnorantN :: Int -> Form
aKnowsBsN n = Conj [ alice `Kw` (bob `hasCard` k) | k <- nCards n ]
bKnowsAsN n = Conj [ bob `Kw` (alice `hasCard` k) | k <- nCards n ]
cIgnorantN n = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i <- nCards n ]

checkSetFor :: RusCardProblem -> [[Int]] -> Bool
checkSetFor (na,nb,nc) set = reachesOn plan rcGoal (rusSCNfor (na,nb,nc)) where
  n = na + nb + nc
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` last (nCards n))
  plan = [ aliceSays, bobSays ]

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

dontChange :: [Form] -> K.RelBDD
dontChange fs = conSet <$> sequence [ equ <$> K.mvBdd b <*> K.cpBdd b | b <- map boolBddOf fs ]

noDoubles :: Int -> Form
noDoubles n = Neg $ Disj [ notDouble k | k <- nCards n ] where
  notDouble k = Conj [alice `hasCard` k, bob `hasCard` k]

rusBelScnfor :: RusCardProblem -> K.BelScene
rusBelScnfor (na,nb,nc) = (K.BlS props law (fromList [ (i, obsbdd i) | i <- rcPlayers ]), defaultDeal) where
  n = na + nb + nc
  props   = [ P k | k <-[0..((2 * n)-1)] ]
  law = boolBddOf $ Conj [ noDoubles n, distribute (na,nb,nc)  ]
  obsbdd "Alice" = dontChange [ PrpF (P $ 2*k) | k <- [0..(n-1)] ]
  obsbdd "Bob"   = dontChange [ PrpF (P $ (2*k) + 1) | k <- [0..(n-1)] ]
  obsbdd "Carol" = dontChange [ Disj [PrpF (P $ 2*k), PrpF (P $ (2*k) + 1)] | k <- [0..(n-1)] ]
  obsbdd _       = error "Unkown Agent"
  defaultDeal =  [ let (PrpF p) = i `hasCard` k in p | i <- [alice,bob], k <- cardsFor i ] where
    cardsFor "Alice" = [0..(na-1)]
    cardsFor "Bob"   = [na..(na+nb-1)]
    cardsFor "Carol" = [(na+nb)..(na+nb+nc-1)]
    cardsFor _       = error "Unkown Agent"
