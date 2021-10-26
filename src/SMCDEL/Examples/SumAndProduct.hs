module SMCDEL.Examples.SumAndProduct where

import Data.List
import Data.Maybe

import SMCDEL.Language
import SMCDEL.Internal.Help
import SMCDEL.Symbolic.S5

-- possible pairs 1<x<y, x+y<=100
pairs :: [(Int, Int)]
pairs = [(x,y) | x<-[2..100], y<-[2..100], x<y, x+y<=100]

-- 7 propositions to label [2..100], because 2^6 = 64 < 100 < 128 = 2^7
xProps, yProps, sProps, pProps :: [Prp]
xProps = [(P  1)..(P  7)]
yProps = [(P  8)..(P 14)]
sProps = [(P 15)..(P 21)]
-- 12 propositions for the product, because 2^11 = 2048 < 2500 < 4096 = 2^12
pProps = [(P 22)..(P 33)]

sapAllProps :: [Prp]
sapAllProps = sort $ xProps ++ yProps ++ sProps ++ pProps

xIs, yIs, sIs, pIs :: Int -> Form
xIs n = booloutofForm (powerset xProps !! n) xProps
yIs n = booloutofForm (powerset yProps !! n) yProps
sIs n = booloutofForm (powerset sProps !! n) sProps
pIs n = booloutofForm (powerset pProps !! n) pProps

xyAre :: (Int,Int) -> Form
xyAre (n,m) = Conj [ xIs n, yIs m ]

sapKnStruct :: KnowStruct
sapKnStruct = KnS sapAllProps law obs where
  law = boolBddOf $ Disj [ Conj [ xyAre (x,y), sIs (x+y), pIs (x*y) ] | (x,y) <- pairs ]
  obs = [ (alice, sProps), (bob, pProps) ]

sapKnows :: Agent -> Form
sapKnows i = Disj [ K i (xyAre p) | p <- pairs ]

sapForm1, sapForm2, sapForm3 :: Form
sapForm1 = K alice $ Neg (sapKnows bob) -- Sum: I knew that you didn't know the numbers.
sapForm2 = sapKnows bob   -- Product: Now I know the two numbers
sapForm3 = sapKnows alice -- Sum: Now I know the two numbers too

sapProtocol :: Form
sapProtocol = Conj [ sapForm1
                   , PubAnnounce sapForm1 sapForm2
                   , PubAnnounce sapForm1 (PubAnnounce sapForm2 sapForm3) ]

sapSolutions :: [[Prp]]
sapSolutions = whereViaBdd sapKnStruct sapProtocol

sapExplainState :: [Prp] -> String
sapExplainState truths = concat
  [ "x = ", explain xProps
  , ", y = ", explain yProps
  , ", x+y = ", explain sProps
  , " and x*y = ", explain pProps ] where
  explain = show . nmbr truths

nmbr :: [Prp] -> [Prp] -> Int
nmbr truths varProps = fromMaybe (error "Value not found") $
  elemIndex (varProps `intersect` truths) (powerset varProps)
