{- |

-- * Translation tests in S5

In this module we test our implementations for correctness, using
QuickCheck for automation and randomization.

We generate random formulas and then evaluate them on Kripke models
and knowledge structures of which we already know that they are
equivalent. The test algorithm then checks whether the different
methods we implemented agree on the result.
-}

module Main (main) where

import Data.Dynamic (toDyn)
import Data.List (sort)
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5 as Sym
import SMCDEL.Explicit.S5 as Exp
import SMCDEL.Translations.S5
import SMCDEL.Internal.TaggedBDD

-- | Run all tests from this module.
main :: IO ()
main = hspec $
  describe "SMCDEL.Translations" $ do
    prop "semantic equivalence"     semanticEquivTest
    prop "semantic validity"        semanticValidTest
    prop "lemma equivalence Kripke" lemmaEquivTestKr
    prop "lemma equivalence KnS"    lemmaEquivTestKnS
    prop "number of states"         numOfStatesTest
    prop "public announcement"      (\ sf sg -> alleq $ pubAnnounceTest sf sg)
    prop "group announcement"       (\ sf gl sg  -> alleq $ groupAnnounceTest sf gl sg)
    prop "single action"            (\am f -> alleq $ singleActionTest am f)
    prop "propulations"             propulationTest

-- * Semantic Equivalence


-- | A Kripke model where Alice knows everything and the other agents do not know anything.
mymodel :: PointedModelS5
mymodel = (KrMS5 ws rel val, 0) where
  buildTable partrows p = [ (p,v):pr | v <- [True,False], pr <- partrows ]
  table = foldl buildTable [[]] [P 0 .. P 4]
  val   = zip [0..] (map sort table)
  ws    = map fst val
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..5::Int] ]

-- | Knowledge structure equivalent to `mymodel`.
myscn :: KnowScene
myscn = (KnS ps (boolBddOf Top) (("0",ps):[(show i,[]) | i<-[1..5::Int]]) , ps)
  where ps = [P 0 .. P 4]

-- | Check for a given formula whether the implementations of the different
-- semantics and translation methods agree on whether the formula holds in
-- `mymodel` or `myscn`.
semanticEquivTest :: Form -> Bool
semanticEquivTest f = alleq
  [ Exp.eval mymodel f                      -- evaluate directly on Kripke
  , Sym.eval myscn (simplify f)             -- evaluate directly on KNS (slow!)
  , Sym.evalViaBdd myscn f                  -- evaluate equivalent BDD on KNS
  , Exp.eval (knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.evalViaBdd (kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  ]

-- | Same as `semanticEquivTest` but for validity instead of truth.
semanticValidTest :: Form -> Bool
semanticValidTest f = alleq
  [ Exp.valid (fst mymodel) f                      -- evaluate directly on Kripke
  , Sym.validViaBdd (fst myscn) f                  -- evaluate equivalent BDD on KNS
  , Exp.valid (fst $ knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.validViaBdd (fst $ kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  , Sym.whereViaBdd (fst $ kripkeToKns mymodel) f == Sym.statesOf (fst $ kripkeToKns mymodel)
  ]

-- * Tests for conversions

-- | Given a Kripke model, check that the number of states of the resut of
-- `kripkeToKns` is the same as the number of worlds when converting it back
-- to a Kripke model with `knsToKripke`.
-- (It need not be the same as the number of worlds of the original model.)
numOfStatesTest :: KripkeModelS5 -> Bool
numOfStatesTest m@(KrMS5 oldws _ _) = numberOfStates kns == length news where
  scn@(kns, _) = kripkeToKns (m, head oldws)
  (KrMS5 news _ _, _) = knsToKripke scn

-- | Check that a model and the result of `kripkeToKnsWithG` is `equivalentWith`.
lemmaEquivTestKr :: KripkeModelS5 -> Bool
lemmaEquivTestKr m@(KrMS5 ws _ _) = equivalentWith (m, head ws) (kns, g (head ws)) g where
  (kns,g) = kripkeToKnsWithG m

-- | Check that a knowledge structure and the result of `knsToKripkeWithG` are `equivalentWith`.
lemmaEquivTestKnS :: KnowStruct -> Bool
lemmaEquivTestKnS kns = equivalentWith (m, w) (kns, g w) g where
  (m, g) = knsToKripkeWithG kns
  w = head (worldsOf m)

-- * Public and Group Announcements

-- | Public announcements can be done in various ways.
-- This test checks that the results of all methods are the same.
pubAnnounceTest :: SimplifiedForm -> SimplifiedForm -> [Bool]
pubAnnounceTest (SF f) (SF g) =
  [ Exp.eval mymodel (PubAnnounce f g)
  , Sym.eval (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  , let
      precon = Sym.evalViaBdd (kripkeToKns mymodel) f
      action = actionToEvent (pubAnnounceAction (agentsOf mymodel) f)
    in
      not precon || Sym.evalViaBdd (unsafeUpdate (kripkeToKns mymodel) action) g
  , let
      precon = Sym.evalViaBdd (kripkeToKns mymodel) f
    in
      not precon || Sym.evalViaBdd (unsafeUpdate (kripkeToKns mymodel) (pubAnnounceTrf (agentsOf mymodel) f)) g
  , Exp.eval mymodel
    (box (Dyn ("publicly announce " ++ show f)
          (toDyn $ pubAnnounceAction (agentsOf mymodel) f))
      g)
  , Sym.evalViaBdd (kripkeToKns mymodel)
    (box (Dyn ("publicly announce " ++ show f)
          (toDyn $ actionToEvent $ pubAnnounceAction (agentsOf mymodel) f))
      g)
  ]

-- | Semi private-group announcements can be done in various ways.
-- This test checks that the results of all methods are the same.
groupAnnounceTest :: SimplifiedForm -> Group -> SimplifiedForm -> [Bool]
groupAnnounceTest (SF f) (Group listeners) (SF g) =
  [ let -- apply action model to Kripke
      precon   = Exp.eval mymodel f
      action   = groupAnnounceAction (agentsOf mymodel) listeners f
      newModel = update mymodel action
    in not precon || Exp.eval newModel g
  , Exp.eval mymodel
    (box (Dyn ("announce " ++ show f ++ " to " ++ show listeners)
           (toDyn $ groupAnnounceAction (agentsOf mymodel) listeners f))
      g)
  , let -- apply equivalent transformer to equivalent kns
      precon  = Sym.evalViaBdd (kripkeToKns mymodel) f
      equiTrf = actionToEvent (groupAnnounceAction (agentsOf mymodel) listeners f)
      newKns  = update (kripkeToKns mymodel) equiTrf
    in not precon || Sym.evalViaBdd newKns g
  , Sym.evalViaBdd (kripkeToKns mymodel)
    (box (Dyn ("announce " ++ show f ++ " to " ++ show listeners)
           (toDyn $ actionToEvent $ groupAnnounceAction (agentsOf mymodel) listeners f))
      g)
  , Exp.eval mymodel
    (box (Dyn ("announce " ++ show f ++ " to " ++ show listeners)
           (toDyn $ eventToAction $ groupAnnounceTrf (agentsOf mymodel) listeners f))
      g)
  , Sym.evalViaBdd (kripkeToKns mymodel)
    (box (Dyn ("announce " ++ show f ++ " to " ++ show listeners)
           (toDyn $ groupAnnounceTrf (agentsOf mymodel) listeners f))
      g)
  ]

-- * Random Action Models

-- | The Arbitrary instance for action models in module `SMCDEL.Explicit.S5`
-- generates a random action model with four actions. To ensure that it is
-- compatible with all models the actual action token has \(\top\) as precondition.
-- The other three action tokens have random formulas as preconditions.
-- Similar to the model above the first agent can tell the actions apart and
-- everyone else confuses them.
singleActionTest :: ActionModelS5 -> Form -> [Bool]
singleActionTest myact f = [a,b,c,d] where
  a = Exp.eval (update mymodel (myact,0::Action)) f
  b = Sym.evalViaBdd (update (kripkeToKns mymodel) (actionToEvent (myact,0::Action))) f
  c = Exp.eval (update mymodel (eventToAction (actionToEvent (myact,0::Action)))) f
  d = case reduce (actionToEvent (myact,0::Action)) f of
    Nothing -> c
    Just g  -> Sym.evalViaBdd (kripkeToKns mymodel) g

-- TODO: Random Transformers and corresponding Action Models

-- * Tests for Bisimulations

-- | A test for `checkPropu`.
propulationTest :: KripkeModelS5 -> Bool
propulationTest m = checkPropu (allsamebdd (vocabOf kns1)) (fst kns1) (fst kns2) (vocabOf kns1) where
  kns1 = kripkeToKns (m,head $ worldsOf m)
  kns2 = kripkeToKns (knsToKripke kns1)
