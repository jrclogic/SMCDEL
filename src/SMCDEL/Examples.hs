{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}

{- | This module shows how to use SMCDEL as a Haskell library checker.
We create Kripke models as toy examples and convert them to knowledge structures.
-}

module SMCDEL.Examples where

import SMCDEL.Explicit.S5
import SMCDEL.Internal.TaggedBDD
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5

-- * Knowledge and Meta-Knowledge

-- | A Kripke model with two states, where Bob knows that \(p\) is true and Alice does not.
-- Still, Alice knows that Bob knows whether \(p\).
-- This is because in all worlds that Alice confuses with the actual world Bob either knows that \(p\) or he knows that not \(p\).
modelA :: PointedModelS5
modelA = (KrMS5 [0,1] [(alice,[[0,1]]),(bob,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)
$(addSvg 'modelA)

{- $
>>> map (SMCDEL.Explicit.S5.eval modelA) [K bob (PrpF (P 0)), K alice (PrpF (P 0))]
[True,False]

>>> SMCDEL.Explicit.S5.eval modelA (K alice (Kw bob (PrpF (P 0))))
True
-}

-- | A model with three states.
-- Bob knows that \(p\) is true and Alice does not.
-- Additionally here Alice does not even know whether Bob knows whether \(p\).
--
-- >>> SMCDEL.Explicit.S5.eval modelB (K bob (PrpF (P 0)))
-- True
--
-- >>> SMCDEL.Explicit.S5.eval modelB (Kw alice (Kw bob (PrpF (P 0))))
-- False
modelB :: PointedModelS5
modelB =
  (KrMS5
    [0,1,2]
    [(alice,[[0,1,2]]),(bob,[[0],[1,2]])]
    [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ]
  , 0)
$(addSvg 'modelB)

{- $
Let us see how such meta-knowledge (or in this case: meta-ignorance) is reflected in knowledge structures. Both knowledge structures contain one additional observational variable.
-}

-- | The knowledge structure equivalent to `modelA`, obtained using `kripkeToKns`.
knsA :: KnowScene
knsA = kripkeToKns modelA
$(addSvg 'knsA)

-- | The knowledge structure equivalent to `modelB`, obtained using `kripkeToKns`.
knsB :: KnowScene
knsB = kripkeToKns modelB
$(addSvg 'knsB)

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
$(addSvg 'redundantModel)

-- | The knowledge structure equivalent to `redundantModel`.
--
-- >>> myKNS
-- (KnS [P 0,P 2] (ifthenelse (var 0) (var 2) (neg (var 2))) [("Alice",[]),("Bob",[P 2])],[P 0,P 2])
myKNS :: KnowScene
myKNS = kripkeToKns redundantModel
$(addSvg 'myKNS)

{- $
If we transform the knowledge structure `myKNS` back to a Kripke Model, we
get a model which is bisimilar to the first one but has only two states --- the
redundancy is gone. This shows how knowledge structures can be used to find
smaller bisimilar Kripke models.
-}

-- | Kripke model equivalent to `myKNS`.
-- This is bisimilar to the redundant model:
--
-- >>> checkBisim [(0,0),(1,0),(2,1)] (fst redundantModel) (fst minimizedModel `SMCDEL.Explicit.S5.withoutProps` [toEnum 2])
-- True
minimizedModel :: PointedModelS5
minimizedModel = knsToKripke myKNS
$(addSvg 'minimizedModel)

-- | Result of transforming `minimizedModel` to a knowledge structure again.
minimizedKNS :: KnowScene
minimizedKNS = kripkeToKns minimizedModel
$(addSvg 'minimizedKNS)

-- | A propulation between `myKNS` and `minimizedKNS`.
-- It shows that they are equivalent.
--
-- >>> checkPropu myPropu (fst myKNS) (fst minimizedKNS) (vocabOf myKNS)
-- True
myPropu :: Propulation
myPropu = allsamebdd (vocabOf myKNS)

-- * Announcements

-- | Public announcement of \(p\) as an action model.
examplePaAction :: PointedActionModelS5
examplePaAction = pubAnnounceAction [alice,bob] (PrpF (P 0))
$(addSvg 'examplePaAction)

{- $

>>> actionToEvent examplePaAction
(KnTrf [] (PrpF (P 0)) [] [("Alice",[]),("Bob",[])],[])

-}

-- | A group announcement be defined as an action model with two states.
exampleGroupAnnounceAction :: PointedActionModelS5
exampleGroupAnnounceAction = groupAnnounceAction [alice, bob] [alice] (PrpF (P 0))
$(addSvg 'exampleGroupAnnounceAction)

{- | The knowledge transformer equivalent to `exampleGroupAnnounceAction`.
It uses two atomic propositions which is redundant in the following sense.
But the event law here implies \(p_1 \leftrightarrow p_2\) and the actual event is given by both \(p_1\) and \(p_2\) being added to the current state.
There is no canonical way to avoid such redundancy as long as we use the general `actionToEvent` function to translate action models to knowledge transformers.
It first adds a set of propositions to label all actions, then additional new observational variables are used to enumerate all equivalence classes for all agents.
-}
exampleGrAnnEvent :: Event
exampleGrAnnEvent = actionToEvent exampleGroupAnnounceAction
$(addSvg 'exampleGrAnnEvent)

-- | Result of turning the knowledge transformer `exampleGrAnnEvent` back to an action model.
-- This is the same as the action model `exampleGroupAnnounceAction` we started with, up to a renaming of action \(1\) to \(3\).
exampleGrAnnBack :: PointedActionModelS5
exampleGrAnnBack = eventToAction (actionToEvent exampleGroupAnnounceAction)

-- * Equivalent Action Models

-- | An action model.
actionOne :: PointedActionModelS5
actionOne = (ActMS5 [(0,(p,[])),(1, (Disj [q, Neg q],[]))] [("Alice",[[0],[1]]), ("Bob",[[0,1]])], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)
$(addSvg 'actionOne)

eventOne :: Event
eventOne = actionToEvent actionOne
$(addSvg 'eventOne)

-- | Another action model which has bisimilar (in fact identical!) effects as `actionOne` on any Kripke model.
actionTwo :: PointedActionModelS5
actionTwo = (ActMS5 [(0,(p,[])),(1,(q,[])),(2,(Neg q,[]))] [("Alice",[[0],[1,2]]), ("Bob",[[0,1,2]]) ], 0) where (p,q) = (PrpF $ P 0, PrpF $ P 1)
$(addSvg 'actionTwo)

-- | Event equivalent to `actionTwo`
eventTwo :: Event
eventTwo = actionToEvent actionTwo
$(addSvg 'eventTwo)
