module Main where

import Data.List (sort)
import Test.Hspec
import Test.Hspec.QuickCheck
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5 as Sym
import SMCDEL.Explicit.S5 as Exp
import SMCDEL.Translations.S5
import SMCDEL.Examples

main :: IO ()
main = hspec $
  describe "SMCDEL.Translations" $ do
    prop "semantic equivalence"     semanticEquivTest
    prop "semantic validity"        semanticValidTest
    prop "lemma equivalence Kripke" lemmaEquivTestKr
    prop "number of states"         numOfStatesTest
    prop "public announcement"      pubAnnounceTest
    prop "group announcement"       (\sf gl sg  -> alleq $ announceTest sf gl sg)
    prop "single action"            (\am f -> alleq $ singleActionTest am f)

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
lemmaEquivTestKr m@(KrMS5 ws _ _) = equivalentWith pm kns g where
  pm = (m, head ws)
  (kns,g) = kripkeToKnsWithG pm

lemmaEquivTestKns :: KnowStruct -> Bool
lemmaEquivTestKns kns = equivalentWith pm scn g where
  scn = (kns, head $ statesOf kns)
  (pm,g) = knsToKripkeWithG scn

pubAnnounceTest :: Prp -> SimplifiedForm -> Bool
pubAnnounceTest prp (SF g) = alleq
  [ Exp.eval mymodel (PubAnnounce f g)
  , Sym.eval (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction (agentsOf mymodel) f))) g
  ] where
      f = PrpF prp

announceTest :: SimplifiedForm -> Group -> SimplifiedForm -> [Bool]
announceTest (SF f) (Group listeners) (SF g) =
  [ Exp.eval mymodel (Announce listeners f g) -- directly on Kripke
  , let -- apply action model to Kripke
      precon   = Exp.eval mymodel f
      action   = groupAnnounceAction (agentsOf mymodel) listeners f
      newModel = productUpdate mymodel action
    in not precon || Exp.eval newModel g
  , Sym.eval (kripkeToKns mymodel) (Announce listeners f g) -- on equivalent kns
  , Sym.evalViaBdd (kripkeToKns mymodel) (Announce listeners f g) -- BDD on equivalent kns
  , let -- apply equivalent transformer to equivalent kns
      precon  = Sym.eval (kripkeToKns mymodel) f
      equiTrf = actionToEvent (groupAnnounceAction (agentsOf mymodel) listeners f)
      newKns  = knowTransform (kripkeToKns mymodel) equiTrf
    in not precon || Sym.eval newKns g
  ]

singleActionTest :: ActionModel -> Form -> [Bool]
singleActionTest myact f = [a,b,c,d] where
  a = Exp.eval (productUpdate mymodel (myact,0)) f
  b = Sym.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent (myact,0))) f
  c = Exp.eval (productUpdate mymodel (eventToAction (actionToEvent (myact,0)))) f
  d = case reduce (actionToEvent (myact,0)) f of
    Nothing -> c
    Just g  -> Sym.evalViaBdd (kripkeToKns mymodel) g
