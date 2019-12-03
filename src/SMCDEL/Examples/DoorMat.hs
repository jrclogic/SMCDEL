module SMCDEL.Examples.DoorMat where

import SMCDEL.Explicit.S5 as Exp hiding (announce)
import SMCDEL.Language
import SMCDEL.Symbolic.S5 hiding (announce)
import SMCDEL.Translations.S5
import SMCDEL.Other.Planning

explain :: Prp -> String
explain (P 1) = "key-under-mat"
explain (P 2) = "bob-has-key"
explain (P k) = "prop-" ++ show k

dmStart :: MultipointedKnowScene
dmStart = (KnS voc law obs, cur) where
  voc = [ P 1, P 2 ]
  law = boolBddOf $ Neg $ PrpF $ P 2 -- it is common knowledge that Bob has no key
  obs = [ ("Anne",[P 1]), ("Bob",[ ]) ] -- Anne knows whether the key is under the mat
  cur = boolBddOf $ PrpF (P 1) -- actually, the key is under the mat

tryTake :: MultipointedEvent
tryTake = (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top) where
  addprops    = [P 3]
  addlaw      = PrpF (P 3) `Equi` PrpF (P 1)
  changeLaw   = [ (P 1, boolBddOf $ Conj [PrpF (P 3) `Impl` Bot, Neg (PrpF (P 3)) `Impl` PrpF (P 1)])
                , (P 2, boolBddOf $ Conj [PrpF (P 3) `Impl` Top, Neg (PrpF (P 3)) `Impl` PrpF (P 2)]) ]
  addObs      = [ ("Anne",[]), ("Bob",[P 3]) ]


tryTakeL :: Labelled MultipointedEvent
tryTakeL = ("tryTake", tryTake)

dmGoal :: Form
dmGoal = PrpF (P 2) -- Bob should get the key!

dmTask :: Task MultipointedKnowScene MultipointedEvent
dmTask = Task dmStart [("tryTake",tryTake)] dmGoal

dmResult :: MultipointedKnowScene
dmResult =  dmStart `update` tryTake

dmResultKripke :: MultipointedModelS5
dmResultKripke = knsToKripkeMulti dmResult

dmResultBob :: MultipointedKnowScene
dmResultBob = (dmStart `asSeenBy` "Bob") `update` tryTake

dmResultBobKripke :: MultipointedModelS5
dmResultBobKripke = knsToKripkeMulti dmResultBob

dm :: Task MultipointedKnowScene MultipointedEvent
dm = Task dmStart [ tryTakeL ] dmGoal

dmCoop :: CoopTask MultipointedKnowScene MultipointedEvent
dmCoop = CoopTask dmStart [("Bob",tryTakeL)] dmGoal

announce :: MultipointedEvent
announce = ( KnTrf [] (PrpF (P 1)) [] [ ("Anne",[]), ("Bob",[]) ]
           , boolBddOf Top )

announce' :: Labelled MultipointedEvent
announce' = ("announce", announce)

dmCoop2 :: CoopTask MultipointedKnowScene MultipointedEvent
dmCoop2 = CoopTask dmStart [ ("Bob" , tryTakeL )
                           , ("Anne", announce') ] dmGoal

dmPlan2 :: ICPlan MultipointedEvent
dmPlan2 = [ ("Anne",announce'), ("Bob",tryTakeL) ]
