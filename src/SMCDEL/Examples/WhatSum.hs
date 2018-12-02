module SMCDEL.Examples.WhatSum where

import SMCDEL.Examples.SumAndProduct (nmbr)
import SMCDEL.Language
import SMCDEL.Internal.Help
import SMCDEL.Symbolic.S5

wsBound :: Int
wsBound = 50

wsTriples :: [ (Int,Int,Int) ]
wsTriples = filter
  ( \(x,y,z) -> x+y==z || x+z==y || y+z==x )
  [ (x,y,z) | x <- [1..wsBound], y <- [1..wsBound], z <- [1..wsBound] ]

aProps,bProps,cProps :: [Prp]
(aProps,bProps,cProps) = ([(P 1)..(P k)],[(P $ k+1)..(P l)],[(P $ l+1)..(P m)]) where
  [k,l,m] = map (wsAmount*) [1,2,3]
  wsAmount = ceiling (logBase 2 (fromIntegral wsBound) :: Double)

aIs, bIs, cIs :: Int -> Form
aIs n = booloutofForm (powerset aProps !! n) aProps
bIs n = booloutofForm (powerset bProps !! n) bProps
cIs n = booloutofForm (powerset cProps !! n) cProps

wsKnStruct :: KnowStruct
wsKnStruct = KnS wsAllProps law obs where
  wsAllProps = aProps++bProps++cProps
  law = boolBddOf $ Disj [ Conj [ aIs x, bIs y, cIs z ] | (x,y,z) <- wsTriples ]
  obs = [ (alice, bProps++cProps), (bob, aProps++cProps), (carol, aProps++bProps) ]

wsKnowSelfA,wsKnowSelfB,wsKnowSelfC :: Form
wsKnowSelfA = Disj [ K alice $ aIs x | x <- [1..wsBound] ]
wsKnowSelfB = Disj [ K bob   $ bIs x | x <- [1..wsBound] ]
wsKnowSelfC = Disj [ K carol $ cIs x | x <- [1..wsBound] ]

wsResult :: KnowStruct
wsResult = foldl update wsKnStruct [ Neg wsKnowSelfA, Neg wsKnowSelfB, Neg wsKnowSelfC ]

wsSolutions :: [State]
wsSolutions = statesOf wsResult

wsExplainState :: [Prp] -> [(Char,Int)]
wsExplainState truths =
  [ ('a', explain aProps), ('b', explain bProps), ('c', explain cProps) ] where
    explain = nmbr truths
