{-# LANGUAGE TemplateHaskell #-}

{- |

We implement the running example from the following reference:

- [EBMN2017]
  Thorsten Engesser, Thomas Bolander, Robert Mattmüuller and Bernhard Nebel (2017):
  /Cooperative Epistemic Multi-Agent Planning for Implicit Coordination/.
  <https://doi.org/10.4204/EPTCS.243.6>

-}

module SMCDEL.Examples.DoorMat where

import SMCDEL.Explicit.S5 as Exp
import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5
import SMCDEL.Other.Planning

-- * Initial Structure

explain :: Prp -> String
explain (P 1) = "key-under-mat"
explain (P 2) = "bob-has-key"
explain (P k) = "prop-" ++ show k

-- | The start of the planning task.
-- It is common knowledge that Bob has no key.
-- Anne knows whether the key is under the mat.
-- And in the actual state the key is under the mat.
dmStart :: MultipointedKnowScene
dmStart = (KnS voc law obs, cur) where
  voc = [ P 1, P 2 ]
  law = boolBddOf $ Neg $ PrpF $ P 2 -- it is common knowledge that Bob has no key
  obs = [ ("Anne",[P 1]), ("Bob",[ ]) ] -- Anne knows whether the key is under the mat
  cur = boolBddOf $ PrpF (P 1) -- actually, the key is under the mat
$(addSvg 'dmStart)

-- * Actions

-- | A transformer modelling that Bob tries to take the key.
-- Uses `P 3` to distinguish two possible events.
tryTake :: MultipointedEvent
tryTake = (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top) where
  addprops    = [P 3]
  addlaw      = PrpF (P 3) `Equi` PrpF (P 1)
  changeLaw   = [ (P 1, boolBddOf $ Conj [PrpF (P 3) `Impl` Bot, Neg (PrpF (P 3)) `Impl` PrpF (P 1)])
                , (P 2, boolBddOf $ Conj [PrpF (P 3) `Impl` Top, Neg (PrpF (P 3)) `Impl` PrpF (P 2)]) ]
  addObs      = [ ("Anne",[]), ("Bob",[P 3]) ]
$(addSvg 'tryTake)

tryTakeL :: Labelled MultipointedEvent
tryTakeL = ("tryTake", tryTake)

dmGoal :: Form
dmGoal = PrpF (P 2) -- Bob should get the key!

-- | The planning task consisting of `dmStart`, `tryTake` as the only action and `dmGoal`.
dmTask :: Task MultipointedKnowScene MultipointedEvent
dmTask = Task dmStart [("tryTake",tryTake)] dmGoal

-- * Simple Solution

-- | Result of updating `dmStart` with `tryTake`.
dmResult :: MultipointedKnowScene
dmResult =  dmStart `update` tryTake
$(addSvg 'dmResult)

dmResultKripke :: MultipointedModelS5
dmResultKripke = knsToKripkeMulti dmResult
$(addSvg 'dmResultKripke)

{- $
In the last model Bob got the key in the actual world.
But before the action he did not know that this plan would succced.
-}

dmResultBob :: MultipointedKnowScene
dmResultBob = (dmStart `asSeenBy` "Bob") `update` tryTake
$(addSvg 'dmResultBob)

-- | The result of the `tryTake` action as predicted by Bob.
-- Note that there are two actual worlds.
dmResultBobKripke :: MultipointedModelS5
dmResultBobKripke = knsToKripkeMulti dmResultBob
$(addSvg 'dmResultBobKripke)

{-$
>>> snd ((dmStart `asSeenBy` "Bob") `asSeenBy` "Anne")
top

>>> reachesOn (Do "tryTake" tryTake (Check dmGoal Stop)) dmGoal dmStart
True
-}

-- * Implicit Coordination

dm :: Task MultipointedKnowScene MultipointedEvent
dm = Task dmStart [ tryTakeL ] dmGoal

dmCoop :: CoopTask MultipointedKnowScene MultipointedEvent
dmCoop = CoopTask dmStart [("Bob",tryTakeL)] dmGoal

{- $

>>> findPlan 3 dm
[Do "tryTake" (KnTrf [P 3] (Equi (PrpF (P 3)) (PrpF (P 1))) [(P 1,ifthenelse (var 1) (neg (var 3)) bot),(P 2,ifthenelse (var 2) top (var 3))] [("Anne",[]),("Bob",[P 3])],top) Stop]

However, this is not an implicitly coordinated (ic) plan:

>>> icSolves [("Bob",tryTakeL)] dmCoop
False

If Anne were the one to execute tryTake, then it would be an ic plan:

>>> [("Anne",tryTakeL)] `icSolves` (CoopTask dmStart [("Anne",tryTakeL)] dmGoal)
True

For the implicitly coordinated plan that actually solves the problem
we also need an announce action.
-}

announce :: MultipointedEvent
announce = ( KnTrf [] (PrpF (P 1)) [] [ ("Anne",[]), ("Bob",[]) ]
           , boolBddOf Top )

announce' :: Labelled MultipointedEvent
announce' = ("announce", announce)

dmCoop2 :: CoopTask MultipointedKnowScene MultipointedEvent
dmCoop2 = CoopTask dmStart [ ("Bob" , tryTakeL )
                           , ("Anne", announce') ] dmGoal

-- | Implicitly coordinated solution to the planning problem.
--
-- >>> dmPlan2 `icSolves` dmCoop2
-- True
dmPlan2 :: ICPlan MultipointedEvent
dmPlan2 = [ ("Anne",announce'), ("Bob",tryTakeL) ]

-- TODO implement findPlanIC to find implicitly coordinated plans
