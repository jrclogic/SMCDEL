
module Main where
import Control.Monad
import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Test
import Text.Printf
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD
import SMCDEL.Explicit.Simple
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
semanticEquivTest f = and [a==b,b==c,c==d,d==e] where
  a = SMCDEL.Explicit.Simple.eval mymodel f                   -- evaluate directly on Kripke
  b = SMCDEL.Symbolic.HasCacBDD.eval myscn f                  -- evaluate directly on KNS
  c = SMCDEL.Symbolic.HasCacBDD.evalViaBdd myscn f            -- evaluate boolean equivalent on KNS
  d = SMCDEL.Explicit.Simple.eval (knsToKripke myscn) f       -- evaluate on corresponding Kripke
  e = SMCDEL.Symbolic.HasCacBDD.eval (kripkeToKns mymodel) f  -- evaluate on corresponding KNS

pubAnnounceTest :: Prp -> Form -> Bool
pubAnnounceTest prp g = (a==b) && (b==c) && (c==d) where
  f = PrpF prp
  a = SMCDEL.Explicit.Simple.eval mymodel (PubAnnounce f g)
  b = SMCDEL.Symbolic.HasCacBDD.eval (kripkeToKns mymodel) (PubAnnounce f g)
  c = SMCDEL.Symbolic.HasCacBDD.evalViaBdd (kripkeToKns mymodel) (PubAnnounce f g)
  d = SMCDEL.Symbolic.HasCacBDD.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction (map show [1..(5::Int)]) f))) g

announceTest :: Form -> [AgAgent] -> Form -> Bool
announceTest f agags g = (a==b) && (b==c) && (c==d) where
  ags = map (\(Ag i) -> i) agags
  a = SMCDEL.Explicit.Simple.eval mymodel (Announce ags f g)
  b = SMCDEL.Symbolic.HasCacBDD.eval (kripkeToKns mymodel) (Announce ags f g)
  c = SMCDEL.Symbolic.HasCacBDD.evalViaBdd (kripkeToKns mymodel) (Announce ags f g)
  d = not (SMCDEL.Symbolic.HasCacBDD.eval (kripkeToKns mymodel) f)
      || SMCDEL.Symbolic.HasCacBDD.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (groupAnnounceAction (map show [1..(5::Int)]) ags f))) g

instance Arbitrary ActionModel where
  arbitrary = do
    f <- arbitrary
    g <- arbitrary
    h <- arbitrary
    return $
      ActM [0..3] [(0,Top),(1,f),(2,g),(3,h)] ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3::Int]]) | k<-[1..5::Int] ])

singleActionTest :: ActionModel -> Form -> Bool
singleActionTest myact f = a==b where
  a = SMCDEL.Explicit.Simple.eval (productUpdate mymodel (myact,0)) f
  b = SMCDEL.Symbolic.HasCacBDD.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent (myact,0))) f

main :: IO ()
main  = do
  results <- mapM (\(s,a) -> printf "%-25s: " s >> a)
    [ ("semanticEquivTest", quickCheckResult semanticEquivTest)
    , ("pubAnnounceTest"  , quickCheckResult pubAnnounceTest  )
    , ("announceTest"     , quickCheckResult announceTest     )
    , ("singleActionTest" , quickCheckResult singleActionTest ) ]
  unless (all isSuccess results) exitFailure
