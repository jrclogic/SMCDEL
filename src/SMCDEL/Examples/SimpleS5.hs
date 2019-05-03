module SMCDEL.Examples.SimpleS5 where

import Data.List ((\\))

import SMCDEL.Explicit.S5
import SMCDEL.Translations.S5
import SMCDEL.Symbolic.S5
import SMCDEL.Language

myStart :: KnowScene
myStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])

publicMakeFalse :: [Agent] -> Prp -> Event
publicMakeFalse agents p = (KnTrf [] Top mychangelaw myobs, []) where
  mychangelaw = [ (p,boolBddOf Bot) ]
  myobs = [ (i,[]) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalse (agentsOf myStart) (P 0)

myResult :: KnowScene
myResult = myStart `update` myEvent

exampleStart :: KnowScene
exampleStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])

makeFalseShowTo :: [Agent] -> Prp -> [Agent] -> Event
makeFalseShowTo agents p intheknow = (KnTrf [P 99] Top examplechangelaw exampleobs, []) where
  examplechangelaw = [ (p,boolBddOf $ PrpF (P 99)) ]
  exampleobs = [ (i,[P 99]) | i <- intheknow           ]
            ++ [ (i,[    ]) | i <- agents \\ intheknow ]

exampleEvent :: Event
exampleEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Bob"]

exampleResult :: KnowScene
exampleResult = exampleStart `update` exampleEvent

thirdEvent :: Event
thirdEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Alice"]

thirdResult :: KnowScene
thirdResult = exampleStart `update` thirdEvent

problemPM :: PointedModelS5
problemPM = ( KrMS5 [0,1,2,3] [ (alice,[[0],[1,2,3]]), (bob,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]), (1,[(P 1,True ),(P 2,False)])
  , (2,[(P 1,False),(P 2,True )]), (3,[(P 1,False),(P 2,False)]) ], 1::World )

problemKNS :: KnowScene
problemKNS = kripkeToKns problemPM
