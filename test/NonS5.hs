
module Main where

import Test.QuickCheck
import Test.Hspec
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD as Sym
import SMCDEL.Other.NonS5 as NonS5
import SMCDEL.Other.Change as Change
import Data.Map.Strict (fromList)
import Data.List (sort)

main :: IO ()
main = hspec $ do
  describe "SMCDEL.Other.NonS5" $
    it "nonS5 semantic equivalence" $ property $ alleq . nonS5semanticEquivTest
  describe "SMCDEL.Other.Change" $
    it "single change" $ property (\a f -> alleq $ singleChangeTest a f)

myMod :: NonS5.GeneralPointedModel
myMod = (NonS5.GKM $ fromList wlist, 0) where
  wlist = [ (w, (fromList val, fromList $ relFor val)) | (val,w) <- wvals ]
  vals  = map sort (foldl buildTable [[]] [P 0 .. P 4])
  wvals = zip vals [0..]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor val = [ (show i, map snd $ seesFrom i val) | i <- [0..5::Int] ]
  seesFrom i val = filter (\(val',_) -> samefor i val val') wvals
  samefor 0 ps qs = ps == qs  -- knows everything
  samefor 1 _  _  = False     -- insane
  samefor _ _  _  = True

myScn :: NonS5.GenScenario
myScn =
  let allprops = [P 0 .. P 4]
  in (NonS5.GenKnS allprops
                  (boolBddOf Top)
                  (fromList $ ("0", NonS5.allsamebdd allprops)  -- knows everything
                            : ("1", NonS5.emptyRelBdd)          -- insane
                            : [(show i, NonS5.totalRelBdd) | i<-[2..5::Int]])
     , allprops)

nonS5semanticEquivTest :: SimplifiedForm -> [Bool]
nonS5semanticEquivTest (SF f) =
  [ NonS5.eval myMod f                           -- evaluate directly on Kripke
  , NonS5.evalViaBdd myScn f                     -- evaluate equivalent BDD on KNS
  , NonS5.eval (NonS5.genKns2Krp myScn) f        -- evaluate on corresponding Kripke
  , NonS5.evalViaBdd (NonS5.genKrp2Kns myMod) f  -- evaluate on corresponding KNS
  ]

singleChangeTest :: ChangeModel -> SimplifiedForm -> [Bool]
singleChangeTest myact (SF f) = [a,b,c,d,e] where
  a = NonS5.eval       (productChange             myMod                                 (myact,0)  ) f
  b = NonS5.evalViaBdd (transform     (genKrp2Kns myMod)                 (actionToEvent (myact,0)) ) f
  c = NonS5.eval       (productChange             myMod  (eventToAction' (actionToEvent (myact,0)))) f
  d = NonS5.eval       (productChange (genKns2Krp myScn) (eventToAction' (actionToEvent (myact,0)))) f
  e = NonS5.evalViaBdd (transform                 myScn                  (actionToEvent (myact,0)) ) f
