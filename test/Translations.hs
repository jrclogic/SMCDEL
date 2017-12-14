
module Main where
import Data.List (sort)
import Test.QuickCheck
import Test.Hspec
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD as Sym
import SMCDEL.Explicit.Simple as Exp
import SMCDEL.Translations
import SMCDEL.Examples

main :: IO ()
main = hspec $
  describe "SMCDEL.Translations" $ do
    it "semantic equivalence"     $ property semanticEquivTest
    it "semantic validity"        $ property semanticValidTest
    it "lemma equivalence Kripke" $ property lemmaEquivTestKr
    it "number of states"         $ property numOfStatesTest
    it "public announcement"      $ property pubAnnounceTest
    it "group announcement"       $ property (\sf gl sg  -> alleq $ announceTest sf gl sg)
    it "single action"            $ property (\am f -> alleq $ singleActionTest am f)

mymodel :: PointedModel
mymodel = (KrM ws rel val, 0) where
  buildTable partrows p = [ (p,v):pr | v <- [True,False], pr <- partrows ]
  table = foldl buildTable [[]] [P 0 .. P 4]
  val   = zip [0..] (map sort table)
  ws    = map fst val
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..5::Int] ]

myscn :: Scenario
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

numOfStatesTest :: KripkeModel -> Bool
numOfStatesTest m@(KrM oldws _ _) = numberOfStates kns == length news where
  scn@(kns, _) = kripkeToKns (m, head oldws)
  (KrM news _ _, _) = knsToKripke scn

lemmaEquivTestKr :: KripkeModel -> Bool
lemmaEquivTestKr m@(KrM ws _ _) = equivalentWith pm kns g where
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
singleActionTest myact f = [a,b,c] where
  a = Exp.eval (productUpdate mymodel (myact,0)) f
  b = Sym.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent (myact,0))) f
  c = Exp.eval (productUpdate mymodel (eventToAction (actionToEvent (myact,0)))) f
