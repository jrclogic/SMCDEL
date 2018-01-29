
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Examples where
import Data.List ((\\),sort)
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Explicit.S5
import SMCDEL.Translations.S5

modelA :: PointedModelS5
modelA = (KrMS5 [0,1] [(alice,[[0,1]]),(bob,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)

modelB :: PointedModelS5
modelB =
  (KrMS5
    [0,1,2]
    [(alice,[[0,1,2]]),(bob,[[0],[1,2]])]
    [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ]
  , 0)

knsA, knsB :: KnowScene
knsA = kripkeToKns modelA
knsB = kripkeToKns modelB

redundantModel :: PointedModelS5
redundantModel = (KrMS5 [0,1,2] [(alice,[[0,1,2]]),(bob,[[0,1],[2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

myKNS :: KnowScene
myKNS = kripkeToKns redundantModel

minimizedModel :: PointedModelS5
minimizedModel = knsToKripke myKNS

pubAnnounceAction :: [Agent] -> Form -> PointedActionModel
pubAnnounceAction ags f = (ActM [0] [(0,f)] [ (i,[[0]]) | i <- ags ], 0)

examplePaAction :: PointedActionModel
examplePaAction = pubAnnounceAction [alice,bob] (PrpF (P 0))

groupAnnounceAction :: [Agent] -> [Agent] -> Form -> PointedActionModel
groupAnnounceAction everyone listeners f = (ActM [0,1] [(0,f),(1,Neg f)] actrel, 0)
  where actrel = sort $ [ (i,[[0],[1]]) | i <- listeners ]
                     ++ [ (i,[[0 , 1]]) | i <- everyone \\ listeners ]

exampleGroupAnnounceAction :: PointedActionModel
exampleGroupAnnounceAction = groupAnnounceAction [alice, bob] [alice] (PrpF (P 0))

eGrAnLaw :: Form
exampleGrAnnEvent :: Event
exampleGrAnnEvent@(KnT _ eGrAnLaw _, _) = actionToEvent exampleGroupAnnounceAction

actionOne :: PointedActionModel
actionOne = (ActM [0,1] [(0,p),(1, Disj [q, Neg q])] [("Alice",[[0],[1]]), ("Bob",[[0,1]])], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)

actionTwo :: PointedActionModel
actionTwo = (ActM [0,1,2] [(0,p),(1,q),(2,Neg q)] [("Alice",[[0],[1,2]]), ("Bob",[[0,1,2]]) ], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)
