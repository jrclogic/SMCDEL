
module EXAMPLES where
import Data.List (delete,intersect,(\\),elemIndex)
import Data.Maybe (fromJust)
import DELLANG
import HELP (powerset)
import KNSCAC
import KRIPKEDEL
import SYMDEL

modelA :: PointedModel
modelA = (KrM [0,1] [(alice,[[0,1]]),(bob,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)

modelB :: PointedModel
modelB = (KrM [0,1,2] [(alice,[[0,1,2]]),(bob,[[0],[1,2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

knsA, knsB :: Scenario
knsA = kripkeToKns modelA
knsB = kripkeToKns modelB

redundantModel :: PointedModel
redundantModel = (KrM [0,1,2] [(alice,[[0,1,2]]),(bob,[[0,1],[2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

myKNS :: Scenario
myKNS = kripkeToKns redundantModel

minimizedModel :: PointedModel
minimizedModel = knsToKripke myKNS

pubAnnounceAction :: [Agent] -> Form -> PointedActionModel
pubAnnounceAction ags f = (ActM [0] [(0,f)] [ (i,[[0]]) | i <- ags ], 0)

examplePaAction :: PointedActionModel
examplePaAction = pubAnnounceAction [alice,bob] (PrpF (P 0))

groupAnnounceAction :: [Agent] -> [Agent] -> Form -> PointedActionModel
groupAnnounceAction everyone listeners f = (ActM [0,1] [(0,f),(1,Top)] actrel, 0)
  where actrel = [ (i,[[0],[1]]) | i <- listeners ]
              ++ [ (i,[[0 , 1]]) | i <- everyone \\ listeners ]

exampleGroupAnnounceAction :: PointedActionModel
exampleGroupAnnounceAction = groupAnnounceAction [alice, bob] [alice] (PrpF (P 0))

mudScnInit :: Int -> Int -> Scenario
mudScnInit n m = ( KnS mudProps (boolBddOf Top) [ (show i,delete (P i) mudProps) | i <- [1..n] ], [P 1 .. P m] ) where mudProps = [P 1 .. P n]

myMudScnInit :: Scenario
myMudScnInit = mudScnInit 3 3

knows :: Int -> Form
knows i = Kw (show i) (PrpF $ P i)

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
thirstyScene n = (KnS [P 1..P n] (boolBddOf Top) [ (show i,[P i]) | i <- [1..n] ], [P 1..P n])

myThirstyScene :: Scenario
myThirstyScene = thirstyScene 3

thirstyF :: Int -> Form
thirstyF n = Conj [ Conj [ doesNotKnow k | k <- [1..n] ]
                  , pubAnnounceStack [ doesNotKnow i | i<-[1..(n-1)] ] $ K (show n) allWantBeer ]
  where
    allWantBeer   = Conj [ PrpF $ P k | k <- [1..n] ]
    doesNotKnow i = Neg $ Kw (show i) allWantBeer

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
  obs   = [ (show (1::Int),[P 1, P 4, P 5])
          , (show (2::Int),[P 2, P 4, P 6])
          , (show (3::Int),[P 3, P 5, P 6]) ]
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
  obs = [ (show i, obsfor i) | i<-[1..n] ]
  sharedbitLabels = [ [k,l] | k <- [1..n], l <- [1..n], k<l ] -- n(n-1)/2 shared bits
  sharedbitRel = zip sharedbitLabels [ (P $ n+1) .. ]
  sharedbits =  map snd sharedbitRel
  obsfor i =  P i : map snd (filter (\(label,_) -> i `elem` label) sharedbitRel)

genEveryoneKnowsWhetherNSApaid :: Int -> Form
genEveryoneKnowsWhetherNSApaid n = Conj [ Kw (show i) (PrpF $ P 0) | i <- [1..n] ]

genDcReveal :: Int -> Int -> Form
genDcReveal n i = Xor (map PrpF (fromJust $ lookup (show i) obs)) where (KnS _ _ obs) = genDcKnsInit n

genNobodyknowsWhoPaid :: Int -> Form
genNobodyknowsWhoPaid n =
  Conj [ Impl (PrpF (P i)) (Conj [Neg $ K (show k) (PrpF $ P i) | k <- delete i [1..n] ]) | i <- [1..n] ]

genDcCheckForm :: Int -> Form
genDcCheckForm n =
  pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $
    Conj [ genEveryoneKnowsWhetherNSApaid n, genNobodyknowsWhoPaid n ]

genDcValid :: Int -> Bool
genDcValid n = validViaBdd (genDcKnsInit n) (genDcCheckForm n)

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

-- possible pairs 1<x<y, x+y<=100
pairs :: [(Int, Int)]
pairs = [(x,y) | x<-[2..100], y<-[2..100], x<y, x+y<=100]

-- 7 propositions are enough to label [2..100]
xProps, yProps, sProps, pProps :: [Prp]
xProps = [(P  1)..(P  7)]
yProps = [(P  8)..(P 14)]
sProps = [(P 15)..(P 21)]
pProps = [(P 22)..(P (21+amount))] where amount = ceiling (logBase 2 (50*50) :: Double)

allProps :: [Prp]
allProps = xProps ++ yProps ++ sProps ++ pProps

xIs, yIs, sIs, pIs :: Int -> Form
xIs n = booloutofForm (powerset xProps !! n) xProps
yIs n = booloutofForm (powerset yProps !! n) yProps
sIs n = booloutofForm (powerset sProps !! n) sProps
pIs n = booloutofForm (powerset pProps !! n) pProps

xyAre :: (Int,Int) -> Form
xyAre (n,m) = Conj [ xIs n, yIs m ]

sapKnStruct :: KnowStruct
sapKnStruct = KnS allProps law obs where
  law = boolBddOf $ Disj [ Conj [ xyAre (x,y), sIs (x+y), pIs (x*y) ] | (x,y) <- pairs ]
  obs = [ (alice, sProps), (bob, pProps) ]

sapKnows :: Agent -> Form
sapKnows i = Conj [ xyAre p `Impl` K i (xyAre p) | p <- pairs ]

sapForm1, sapForm2, sapForm3 :: Form

--Sum says: I knew that you didn't know the two numbers.
sapForm1 = K alice $ Neg (sapKnows bob)

--Product says: Now I know the two numbers
sapForm2 = sapKnows bob

--Sum says: Now I know the two numbers too
sapForm3 = sapKnows alice

sapProtocol :: Form
sapProtocol = Conj [ sapForm1
                   , PubAnnounce sapForm1 sapForm2
                   , PubAnnounce sapForm1 (PubAnnounce sapForm2 sapForm3) ]

sapSolutions :: [[Prp]]
sapSolutions = statesOf (KNSCAC.pubAnnounce sapKnStruct sapProtocol)

sapExplainState :: [Prp] -> String
sapExplainState truths = concat [ "x = ", nmbr xProps, ", y = ", nmbr yProps, ", ",
  "x+y = ", nmbr sProps, " and x*y = ", nmbr pProps ] where
    nmbr set = show.fromJust $ elemIndex (set `intersect` truths) (powerset set)
