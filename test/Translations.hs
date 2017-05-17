
module Main where
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
    it "group announcement"       $ property announceTest
    it "single action"            $ property singleActionTest

mymodel :: PointedModel
mymodel = (KrM ws rel (zip ws table), 0) where
  ws    = [0..31]
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..5::Int] ]
  table = foldl buildTable [[]] [P k | k <- [0..4::Int]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

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

pubAnnounceTest :: Prp -> Form -> Bool
pubAnnounceTest prp g = alleq
  [ Exp.eval mymodel (PubAnnounce f g)
  , Sym.eval (kripkeToKns mymodel) (PubAnnounce f sg)
  , Sym.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction (map show [1..(5::Int)]) f))) sg
  ] where
      f = PrpF prp
      sg = simplify g

announceTest :: Form -> Group -> Form -> Bool
announceTest f (Group ags) g = alleq
  [ Exp.eval mymodel (Announce ags f g)
  , Sym.eval (kripkeToKns mymodel) (Announce ags sf sg)
  , Sym.evalViaBdd (kripkeToKns mymodel) (Announce ags f g)
  , not (Sym.eval (kripkeToKns mymodel) sf)
      || Sym.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (groupAnnounceAction (map show [1..(5::Int)]) ags sf))) sg
  ] where [sf,sg] = map simplify [f,g]

singleActionTest :: ActionModel -> Form -> Bool
singleActionTest myact f = a==b && b==c where
  a = Exp.eval (productUpdate mymodel (myact,0)) f
  b = Sym.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent (myact,0))) f
  c = Exp.eval (productUpdate mymodel (eventToAction (actionToEvent (myact,0)))) f
