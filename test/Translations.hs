
-- test/Translations.lhs
module Main where
import Control.Monad
import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Test
import Text.Printf
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD as Sym
-- import qualified SMCDEL.Symbolic.CUDD as SymCUDD -- TODO also check this!
import SMCDEL.Explicit.Simple as Exp
import SMCDEL.Translations
import SMCDEL.Examples

mymodel :: PointedModel
mymodel = (KrM ws rel (zip ws table), 0) where
  ws    = [0..31]
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..5::Int] ]
  table = foldl buildTable [[]] [P k | k<- [0..4::Int]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

myscn :: Scenario
myscn = (KnS ps (boolBddOf Top) (("0",ps):[(show i,[]) | i<-[1..5::Int]]) , ps)
  where ps = [P 0 .. P 4]

semanticEquivTest :: Form -> Bool
semanticEquivTest f = alleq id
  [ Exp.eval mymodel f                      -- evaluate directly on Kripke
  , Sym.eval myscn (simplify f)             -- evaluate directly on KNS (slow!)
  , Sym.evalViaBdd myscn f                  -- evaluate equivalent BDD on KNS
  , Exp.eval (knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.evalViaBdd (kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  ]

semanticValidTest :: Form -> Bool
semanticValidTest f = alleq id
  [ Exp.valid (fst mymodel) f                      -- evaluate directly on Kripke
  , Sym.validViaBdd (fst myscn) f                  -- evaluate equivalent BDD on KNS
  , Exp.valid (fst $ knsToKripke myscn) f          -- evaluate on corresponding Kripke
  , Sym.validViaBdd (fst $ kripkeToKns mymodel) f  -- evaluate on corresponding KNS
  , Sym.whereViaBdd (fst $ kripkeToKns mymodel) f == Sym.statesOf (fst $ kripkeToKns mymodel)
  ]

-- TODO: skip second conversion, use minimization under bisimulation instead
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
pubAnnounceTest prp g = alleq id
  [ Exp.eval mymodel (PubAnnounce f g)
  , Sym.eval (kripkeToKns mymodel) (PubAnnounce f sg)
  , Sym.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  , Sym.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction (map show [1..(5::Int)]) f))) sg
  ] where
      f = PrpF prp
      sg = simplify g

announceTestResults ::  Form -> Group -> Form -> [Bool]
announceTestResults f (Group ags) g =
  [ Exp.eval mymodel (Announce ags f g)
  , Sym.eval (kripkeToKns mymodel) (Announce ags sf sg)
  , Sym.evalViaBdd (kripkeToKns mymodel) (Announce ags f g)
  , not (Sym.eval (kripkeToKns mymodel) sf)
      || Sym.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (groupAnnounceAction (map show [1..(5::Int)]) ags sf))) sg
  ] where [sf,sg] = map simplify [f,g]

announceTest :: Form -> Group -> Form -> Bool
announceTest f agags g = alleq id $ announceTestResults f agags g

singleActionTest :: ActionModel -> Form -> Bool
singleActionTest myact f = a==b && b==c where
  a = Exp.eval (productUpdate mymodel (myact,0)) f
  b = Sym.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent (myact,0))) f
  c = Exp.eval (productUpdate mymodel (eventToAction (actionToEvent (myact,0)))) f

main :: IO ()
main  = do
  putStr "\n"
  results <- mapM (\(s,a) -> printf "%-18s " s >> a)
    [ ("semanticEquivTest", quickCheckResult semanticEquivTest)
    , ("semanticValidTest", quickCheckResult semanticValidTest)
    , ("lemmaEquivTestKr" , quickCheckResult lemmaEquivTestKr )
    , ("numOfStatesTest"  , quickCheckResult numOfStatesTest  )
    -- TODO: instance (Arbitrary KnowStruct)
    -- , ("lemmaEquivTestKns", quickCheckResult lemmaEquivTestKns)
    , ("pubAnnounceTest"  , quickCheckResult pubAnnounceTest  )
    , ("announceTest"     , quickCheckResult announceTest     )
    , ("singleActionTest" , quickCheckResult singleActionTest ) ]
  unless (all isSuccess results) exitFailure
