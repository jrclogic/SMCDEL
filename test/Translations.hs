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
import SMCDEL.Examples
import SMCDEL.Internal.TaggedBDD

main :: IO ()
main = hspec $
  describe "SMCDEL.Translations" $ do
    prop "semantic equivalence"     semanticEquivTest
    prop "semantic validity"        semanticValidTest
    prop "lemma equivalence Kripke" lemmaEquivTestKr
    prop "lemma equivalence KnS"    lemmaEquivTestKnS
    prop "number of states"         numOfStatesTest
    prop "public announcement"      pubAnnounceTest
    prop "group announcement"       (\sf gl sg  -> alleq $ announceTest sf gl sg)
    prop "single action"            (\am f -> alleq $ singleActionTest am f)
    prop "propulations"             propulationTest

mymodel :: PointedModelS5
mymodel = (KrMS5 ws rel val, 0) where
  buildTable partrows p = [ (p,v):pr | v <- [True,False], pr <- partrows ]
  table = foldl buildTable [[]] [P 0 .. P 4]
  val   = zip [0..] (map sort table)
  ws    = map fst val
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..5::Int] ]

myscn :: KnowScene
myscn = (KnS ps (boolBddOf Top) (("0",ps):[(show i,[]) | i<-[1..5::Int]]) , ps)
  where ps = [P 0 .. P 4]

semanticEquivTest :: Form -> Bool
semanticEquivTest f = alleq
  [ Exp.eval mymodel f                      -- evaluate directly on Kripke
  , Sym.eval myscn (simplify f)             -- evaluate directly on KNS (slow!)
  , Sym.evalViaBdd myscn f                  -- evaluate equivalent BDD on KNS
  , Exp.eval (knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.evalViaBdd (kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  ]

semanticValidTest :: Form -> Bool
semanticValidTest f = alleq
  [ Exp.valid (fst mymodel) f                      -- evaluate directly on Kripke
  , Sym.validViaBdd (fst myscn) f                  -- evaluate equivalent BDD on KNS
  , Exp.valid (fst $ knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.validViaBdd (fst $ kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  , Sym.whereViaBdd (fst $ kripkeToKns mymodel) f == Sym.statesOf (fst $ kripkeToKns mymodel)
  ]

numOfStatesTest :: KripkeModelS5 -> Bool
numOfStatesTest m@(KrMS5 oldws _ _) = numberOfStates kns == length news where
  scn@(kns, _) = kripkeToKns (m, head oldws)
  (KrMS5 news _ _, _) = knsToKripke scn

lemmaEquivTestKr :: KripkeModelS5 -> Bool
lemmaEquivTestKr m@(KrMS5 ws _ _) = equivalentWith (m, head ws) (kns, g (head ws)) g where
  (kns,g) = kripkeToKnsWithG m

lemmaEquivTestKnS :: KnowStruct -> Bool
lemmaEquivTestKnS kns = equivalentWith (m, w) (kns, g w) g where
  (m, g) = knsToKripkeWithG kns
  w = head (worldsOf m)

pubAnnounceTest :: Prp -> SimplifiedForm -> Bool
pubAnnounceTest prp (SF g) = alleq
  [ Exp.eval mymodel (PubAnnounce f g)
  , Sym.eval (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.evalViaBdd (update (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction (agentsOf mymodel) f))) g
  , Sym.evalViaBdd (update (kripkeToKns mymodel) (publicAnnounce (agentsOf mymodel) f)) g
  , Exp.eval mymodel (Dia (Dyn dynName (toDyn $ pubAnnounceAction (agentsOf mymodel) f)) g)
  , Sym.evalViaBdd (kripkeToKns mymodel) (Dia (Dyn dynName (toDyn $ actionToEvent $ pubAnnounceAction (agentsOf mymodel) f)) g)
  ] where
      f = PrpF prp
      dynName = "publicly announce " ++ show prp

announceTest :: SimplifiedForm -> Group -> SimplifiedForm -> [Bool]
announceTest (SF f) (Group listeners) (SF g) =
  [ Exp.eval mymodel (Announce listeners f g) -- directly on Kripke
  , let -- apply action model to Kripke
      precon   = Exp.eval mymodel f
      action   = groupAnnounceAction (agentsOf mymodel) listeners f
      newModel = update mymodel action
    in not precon || Exp.eval newModel g
  , Exp.eval mymodel (box (Dyn ("announce " ++ show f ++ " to " ++ show listeners) (toDyn $ groupAnnounceAction (agentsOf mymodel) listeners f)) g)
  , Sym.evalViaBdd (kripkeToKns mymodel) (Announce listeners f g) -- BDD on equivalent kns
  , let -- apply equivalent transformer to equivalent kns
      precon  = Sym.evalViaBdd (kripkeToKns mymodel) f
      equiTrf = actionToEvent (groupAnnounceAction (agentsOf mymodel) listeners f)
      newKns  = update (kripkeToKns mymodel) equiTrf
    in not precon || Sym.evalViaBdd newKns g
  ]

singleActionTest :: ActionModelS5 -> Form -> [Bool]
singleActionTest myact f = [a,b,c,d] where
  a = Exp.eval (update mymodel (myact,0::Action)) f
  b = Sym.evalViaBdd (update (kripkeToKns mymodel) (actionToEvent (myact,0::Action))) f
  c = Exp.eval (update mymodel (eventToAction (actionToEvent (myact,0::Action)))) f
  d = case reduce (actionToEvent (myact,0::Action)) f of
    Nothing -> c
    Just g  -> Sym.evalViaBdd (kripkeToKns mymodel) g

propulationTest :: KripkeModelS5 -> Bool
propulationTest m = checkPropu (allsamebdd (vocabOf kns1)) (fst kns1) (fst kns2) (vocabOf kns1) where
  kns1 = kripkeToKns (m,head $ worldsOf m)
  kns2 = kripkeToKns (knsToKripke kns1)
