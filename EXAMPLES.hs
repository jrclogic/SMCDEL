
module EXAMPLES where
import Data.List (delete,intersect,(\\))
import Data.Maybe (fromJust)
import DELLANG
import KNSCAC
import KRIPKEDEL
import SYMDEL

modelA :: PointedModel
modelA = (KrM [0,1] [(0,[[0,1]]),(1,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)

modelB :: PointedModel
modelB = (KrM [0,1,2] [(0,[[0,1,2]]),(1,[[0],[1,2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

knsA, knsB :: Scenario
knsA = kripkeToKns modelA
knsB = kripkeToKns modelB

redundantModel :: PointedModel
redundantModel = (KrM [0,1,2] [(0,[[0,1,2]]),(1,[[0,1],[2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

myKNS :: Scenario
myKNS = kripkeToKns redundantModel

minimizedModel :: PointedModel
minimizedModel = knsToKripke myKNS

pubAnnounceAction :: [Agent] -> Form -> PointedActionModel
pubAnnounceAction ags f = (ActM [0] [(0,f)] [ (i,[[0]]) | i <- ags ], 0)

examplePaAction :: PointedActionModel
examplePaAction = pubAnnounceAction [0,1] (PrpF (P 0))

groupAnnounceAction :: [Agent] -> [Agent] -> Form -> PointedActionModel
groupAnnounceAction everyone listeners f = (ActM [0,1] [(0,f),(1,Top)] actrel, 0)
  where actrel = [ (i,[[0],[1]]) | i <- listeners ]
              ++ [ (i,[[0 , 1]]) | i <- everyone \\ listeners ]

exampleGroupAnnounceAction :: PointedActionModel
exampleGroupAnnounceAction = groupAnnounceAction [0,1] [0] (PrpF (P 0))

mudScnInit :: Int -> Int -> Scenario
mudScnInit n m = ( KnS mudProps (boolBddOf Top) [ (i,delete (P i) mudProps) | i <- [1..n] ], [P 1 .. P m] ) where mudProps = [P 1 .. P n]

myMudScnInit :: Scenario
myMudScnInit = mudScnInit 3 3

knows :: Int -> Form
knows i = Kw i (PrpF $ P i)

nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

father :: Int -> Form
father n = Disj (map PrpF [P 1 .. P n])
mudScn0 :: Scenario
mudScn0 = pubAnnounceOnScn myMudScnInit (father 3)

mudScn1 :: Scenario
mudScn1 = pubAnnounceOnScn mudScn0 (nobodyknows 3)

mudScn2 :: Scenario
mudKns2 :: KnowStruct
mudScn2@(mudKns2,_) = pubAnnounceOnScn mudScn1 (nobodyknows 3)

thirstyScene :: Int -> Scenario
thirstyScene n = (KnS [P 1..P n] (boolBddOf Top) [ (i,[P i]) | i <- [1..n] ], [P 1..P n])

myThirstyScene :: Scenario
myThirstyScene = thirstyScene 3

thirstyF :: Int -> Form
thirstyF n = Conj [ Conj [ doesNotKnow k | k <- [1..n] ]
		  , pubAnnounceStack [ doesNotKnow i | i<-[1..(n-1)] ] $ K n allWantBeer ]
  where
    allWantBeer   = Conj [ PrpF $ P k | k <- [1..n] ]
    doesNotKnow i = Neg $ Kw i allWantBeer

thirstyCheck :: Int -> Bool
thirstyCheck n = evalViaBdd (thirstyScene n) (thirstyF n)

dcScnInit :: Int -> (Bool,Bool,Bool) -> Scenario
dcScnInit payer (b1,b2,b3) = ( KnS props law obs , truths ) where
  props = [ P 0   -- The NSA paid
	  , P 1   -- Alice paid
	  , P 2   -- Bob paid
	  , P 3   -- Charlie paid
	  , P 4   -- shared bit of Alice and Bob
	  , P 5   -- shared bit of Alice and Charlie
	  , P 6 ] -- shared bit of Bob and Charlie
  law   = boolBddOf $ Conj [ someonepaid, notwopaid ]
  obs   = [ (1,[P 1, P 4, P 5])
	  , (2,[P 2, P 4, P 6])
	  , (3,[P 3, P 5, P 6]) ]
  truths = [ P payer ] ++ [ P 4 | b1 ] ++ [ P 5 | b2 ] ++ [ P 6 | b3 ]

dcScn1 :: Scenario
dcScn1 = dcScnInit 1 (True,True,False)

someonepaid, notwopaid :: Form
someonepaid = Disj (map (PrpF . P) [0..3])
notwopaid = Conj [ Neg $ Conj [ PrpF $ P x, PrpF $ P y ] | x<-[0..3], y<-[(x+1)..3] ]

reveal :: Int -> Form
reveal 1 = Xor (map PrpF [P 1, P 4, P 5])
reveal 2 = Xor (map PrpF [P 2, P 4, P 6])
reveal _ = Xor (map PrpF [P 3, P 5, P 6])

dcScn2 :: Scenario
dcScn2 = pubAnnounceOnScn dcScn1 (Conj [reveal 1, reveal 2, reveal 3])

everyoneKnowsWhetherNSApaid :: Form
everyoneKnowsWhetherNSApaid = Conj [ Kw i (PrpF $ P 0) | i <- [1..3] ]

nobodyknowsWhoPaid :: Form
nobodyknowsWhoPaid = Conj
  [ Impl (PrpF (P 1)) (Conj [Neg $ K 2 (PrpF $ P 1), Neg $ K 3 (PrpF $ P 1) ])
  , Impl (PrpF (P 2)) (Conj [Neg $ K 1 (PrpF $ P 2), Neg $ K 3 (PrpF $ P 2) ])
  , Impl (PrpF (P 3)) (Conj [Neg $ K 1 (PrpF $ P 3), Neg $ K 2 (PrpF $ P 3) ]) ]

dcCheckForm :: Form
dcCheckForm = PubAnnounceW (reveal 1) $ PubAnnounceW (reveal 2) $ PubAnnounceW (reveal 3) $
    Conj [ everyoneKnowsWhetherNSApaid, nobodyknowsWhoPaid ]

dcValid :: Bool
dcValid = validViaBdd dcStruct dcCheckForm where (dcStruct,_) = dcScn1

genSomeonepaid :: Int -> Form
genSomeonepaid n = Disj (map (PrpF . P) [0..n])

genNotwopaid :: Int -> Form
genNotwopaid n = Conj [ Neg $ Conj [ PrpF $ P x, PrpF $ P y ] | x<-[0..n], y<-[(x+1)..n] ]

genDcKnsInit :: Int -> KnowStruct
genDcKnsInit n = KnS props law obs where
  props = [ P 0 ] -- The NSA paid
    ++ [ (P 1) .. (P n) ] -- agent i paid
    ++ sharedbits
  law = boolBddOf $ Conj [genSomeonepaid n, genNotwopaid n]
  obs = [ (i, obsfor i) | i<-[1..n] ]
  sharedbitLabels = [ [k,l] | k <- [1..n], l <- [1..n], k<l ] -- n(n-1)/2 shared bits
  sharedbitRel = zip sharedbitLabels [ (P $ n+1) .. ]
  sharedbits =  map snd sharedbitRel
  obsfor i =  P i : map snd (filter (\(label,_) -> i `elem` label) sharedbitRel)

genEveryoneKnowsWhetherNSApaid :: Int -> Form
genEveryoneKnowsWhetherNSApaid n = Conj [ Kw i (PrpF $ P 0) | i <- [1..n] ]

genDcReveal :: Int -> Int -> Form
genDcReveal n i = Xor (map PrpF (fromJust $ lookup i obs)) where (KnS _ _ obs) = genDcKnsInit n

genNobodyknowsWhoPaid :: Int -> Form
genNobodyknowsWhoPaid n =
  Conj [ Impl (PrpF (P i)) (Conj [Neg $ K k (PrpF $ P i) | k <- delete i [1..n] ]) | i <- [1..n] ]

genDcCheckForm :: Int -> Form
genDcCheckForm n =
  pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $
    Conj [ genEveryoneKnowsWhetherNSApaid n, genNobodyknowsWhoPaid n ]

genDcValid :: Int -> Bool
genDcValid n = validViaBdd (genDcKnsInit n) (genDcCheckForm n)

rcPlayers, rcCards :: [Int]
rcPlayers = [alice,bob,carol]
rcCards   = [0..6]

rcProps :: [Prp]
rcProps   = [ P k | k <-[0..((length rcPlayers * length rcCards)-1)] ]

hasCard :: Agent -> Int -> Form
hasCard i n = PrpF (P (3 * n + i))

allCardsGiven, allCardsUnique :: Form
allCardsGiven  = Conj [ Disj [ i `hasCard` n | i <- rcPlayers ] | n <- rcCards ]
allCardsUnique = Conj [ Neg $ isDouble n | n <- rcCards ] where
  isDouble n = Disj [ Conj [ x `hasCard` n, y `hasCard` n ] | x <- rcPlayers, y <- rcPlayers, x/=y, x<=y ]

distribute331 :: Form
distribute331 = Conj [ aliceAtLeastThree, bobAtLeastThree, carolAtLeastOne ] where
  aliceAtLeastThree = Disj [ Conj (map (alice `hasCard`) [x, y, z]) | x<-rcCards, y<-rcCards, z<-rcCards, x/=y, x/=z, y/=z  ]
  bobAtLeastThree = Disj [ Conj (map (bob `hasCard`) [x, y, z]) | x<-rcCards, y<-rcCards, z<-rcCards, x/=y, x/=z, y/=z  ]
  carolAtLeastOne = Disj [ carol `hasCard` k | k<-[0..6] ]

rusSCN :: Scenario
rusSCN = (KnS rcProps law [ (i, obs i) | i <- rcPlayers ], defaultDeal) where
  law = boolBddOf $ Conj [ allCardsGiven, allCardsUnique, distribute331 ]
  obs i = [ P (3*k+i) | k<-[0..6] ]
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
rcCheck 2 = PubAnnounce aAnnounce (Ck [0,1] bKnowsAs)

rcCheck 3 = PubAnnounce aAnnounce (K 1 (PrpF (P 20)))

rcCheck 4 = PubAnnounce aAnnounce (Ck [0,1,2] cIgnorant)

rcCheck 5 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [0,1] aKnowsBs))
rcCheck 6 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [0,1] bKnowsAs))
rcCheck _ = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [0,1,2] cIgnorant))

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
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck [0,1] $ Conj [aKnowsBs, bKnowsAs]))
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck [0,1,2] cIgnorant)) ]

possibleHands :: [[Int]]
possibleHands = [ [x,y,z] | x <- rcCards, y <- rcCards, z <-rcCards, x < y, y < z ]

pickHands :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHands _ 0 = [ [ [ ] ] ]
pickHands unused 1 = [ [h] | h <- unused ]
pickHands unused n = concat [ [ h:hs | hs <- pickHands (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> length (h `intersect` xs) < 2 && h < xs)

allHandLists :: [ [ [Int] ] ]
allHandLists = concatMap (pickHands possibleHands) [5,6,7]
