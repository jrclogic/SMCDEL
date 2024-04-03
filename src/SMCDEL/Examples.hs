{- | This module shows how to use the SMCDEL model checker and the translations with some toy examples.

-}

{-# LANGUAGE FlexibleInstances #-}

module SMCDEL.Examples where

import Data.List ((\\),sort)

import SMCDEL.Explicit.S5
import SMCDEL.Internal.TaggedBDD
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5

-- * Knowledge and Meta-Knowledge

-- | A Kripke model with two states, where Bob knows that \(p\) is true and Alice does not.
-- Still, Alice knows that Bob knows whether \(p\).
-- This is because in all worlds that Alice confuses with the actual world Bob either knows that \(p\) or he knows that not \(p\).
modelA :: PointedModelS5
modelA = (KrMS5 [0,1] [(alice,[[0,1]]),(bob,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)

-- | A model with three states.
-- Bob knows that \(p\) is true and Alice does not.
-- Additionally here Alice does not even know whether Bob knows whether \(p\).
modelB :: PointedModelS5
modelB =
  (KrMS5
    [0,1,2]
    [(alice,[[0,1,2]]),(bob,[[0],[1,2]])]
    [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ]
  , 0)

-- | The knowledge structure equivalent to `modelA`, obtained using `kripkeToKns`.
knsA :: KnowScene
knsA = kripkeToKns modelA

-- | The knowledge structure equivalent to `modelB`, obtained using `kripkeToKns`.
knsB :: KnowScene
knsB = kripkeToKns modelB

{- $
The only difference is in the state law of the knowledge structures.
Remember that this component determines which assignments are states of this knowledge structure.
In our implementation this is not a formula but a BDD, hence we show its graph here.
The BDD in `knsA` demands that the propositions \(p\) and \(p_2\) have the same value.
Hence knsA has just two states while `knsB` has three:

>>> let (structA,foo) = knsA in statesOf structA
[[P 0,P 2],[]]

>>> let (structB,foo) = knsB in statesOf structB
[[P 0],[P 0,P 2],[]]

-}

-- * Minimization via Translation

-- | A Kripke model with three states 0,1,2 where 0 and 1 are bisimilar --- it is redundant.
redundantModel :: PointedModelS5
redundantModel = (KrMS5 [0,1,2] [(alice,[[0,1,2]]),(bob,[[0,1],[2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

-- | The knowledge structure equivalent to `redundantModel`.
myKNS :: KnowScene
myKNS = kripkeToKns redundantModel

minimizedModel :: PointedModelS5
minimizedModel = knsToKripke myKNS

minimizedKNS :: KnowScene
minimizedKNS = kripkeToKns minimizedModel

-- | A propulation between `myKNS` and `minimizedKNS`.
myPropu :: Propulation
myPropu = allsamebdd (vocabOf myKNS)


-- * Different Announcements

-- | Public announcement as an action model.
pubAnnounceAction :: [Agent] -> Form -> PointedActionModelS5
pubAnnounceAction ags f = (ActMS5 [(0,(f,[]))] [ (i,[[0]]) | i <- ags ], 0)

examplePaAction :: PointedActionModelS5
examplePaAction = pubAnnounceAction [alice,bob] (PrpF (P 0))

-- | Group announcement as an action model.
groupAnnounceAction :: [Agent] -> [Agent] -> Form -> PointedActionModelS5
groupAnnounceAction everyone listeners f = (ActMS5 [(0,(f,[])),(1,(Neg f,[]))] actrel, 0)
  where actrel = sort $ [ (i,[[0],[1]]) | i <- listeners ]
                     ++ [ (i,[[0 , 1]]) | i <- everyone \\ listeners ]

exampleGroupAnnounceAction :: PointedActionModelS5
exampleGroupAnnounceAction = groupAnnounceAction [alice, bob] [alice] (PrpF (P 0))

eGrAnLaw :: Form
exampleGrAnnEvent :: Event
exampleGrAnnEvent@(KnTrf _ eGrAnLaw _ _, _) = actionToEvent exampleGroupAnnounceAction

-- * Equivalent Action Models

-- | An action model.
actionOne :: PointedActionModelS5
actionOne = (ActMS5 [(0,(p,[])),(1, (Disj [q, Neg q],[]))] [("Alice",[[0],[1]]), ("Bob",[[0,1]])], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)

-- | Another action model which has bisimilar (in fact identical!) effects as `actionOne` on any Kripke model.
actionTwo :: PointedActionModelS5
actionTwo = (ActMS5 [(0,(p,[])),(1,(q,[])),(2,(Neg q,[]))] [("Alice",[[0],[1,2]]), ("Bob",[[0,1,2]]) ], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)
