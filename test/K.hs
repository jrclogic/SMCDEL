module Main (main) where

import Data.Dynamic (toDyn)
import Data.Map.Strict (fromList)
import Data.List (sort)
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Explicit.S5 (Action)
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Explicit.K as ExpK
import SMCDEL.Symbolic.K as SymK
import SMCDEL.Translations.K as TransK

main :: IO ()
main = hspec $ do
  describe "hardcoded myMod and myScn" $ do
    prop "semanticEquivalence" $ alleq . semanticEquivalenceTest
    prop "singleChange: random action model with change" $ \ a f -> alleq $ singleChangeTest a f
  describe "random Kripke models" $ do
    prop "Ck i -> K i" $ \(Ag i) krm f -> ExpK.eval (krm,0) (Ck [i] f `Impl` Ck [i] f)
    prop "semanticEquivExpToSym" $ \krm f -> alleq $ semanticEquivExpToSym (krm,0) f
    prop "diff" $ \krmA krmB -> diffTest (krmA,0) (krmB,0)
  describe "random belief structures" $
    prop "semanticEquivSymToExp" $ \bls f -> alleq $ semanticEquivSymToExp (bls, head (statesOf bls)) f

myMod :: ExpK.PointedModel
myMod = (ExpK.KrM $ fromList wlist, 0) where
  wlist = [ (w, (fromList val, fromList $ relFor val)) | (val,w) <- wvals ]
  vals  = map sort (foldl buildTable [[]] [P 0 .. P 4])
  wvals = zip vals [0..]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor val = [ (show i, map snd $ seesFrom i val) | i <- [0..5::Int] ]
  seesFrom i val = filter (\(val',_) -> samefor i val val') wvals
  samefor 0 ps qs = ps == qs  -- knows everything
  samefor 1 _  _  = False     -- insane
  samefor _ _  _  = True

myScn :: SymK.BelScene
myScn =
  let allprops = [P 0 .. P 4]
  in (SymK.BlS allprops
                  (boolBddOf Top)
                  (fromList $ ("0", SymK.allsamebdd allprops)  -- knows everything
                            : ("1", SymK.emptyRelBdd)          -- insane
                            : [(show i, SymK.totalRelBdd) | i<-[2..5::Int]])
     , allprops)

semanticEquivalenceTest :: SimplifiedForm -> [Bool]
semanticEquivalenceTest (SF f) =
  [ ExpK.eval myMod f                            -- evaluate directly on Kripke
  , SymK.evalViaBdd myScn f                      -- evaluate equivalent BDD on BlS
  , ExpK.eval (TransK.blsToKripke myScn) f        -- evaluate on corresponding Kripke
  , SymK.evalViaBdd (TransK.kripkeToBls myMod) f  -- evaluate on corresponding BlS
  ]

singleChangeTest :: ActionModel -> SimplifiedForm -> [Bool]
singleChangeTest myact (SF f) =
  [ not (ExpK.eval                            myMod  (preOf                               (myact,0::Action)))
      || ExpK.eval       (update              myMod                                       (myact,0::Action)  ) f
  , not (SymK.evalViaBdd         (kripkeToBls myMod) (preOf                (actionToEvent (myact,0))))
      || SymK.evalViaBdd (update (kripkeToBls myMod)                       (actionToEvent (myact,0)))  f
  , not (ExpK.eval                            myMod  (preOf (eventToAction (actionToEvent (myact,0)))))
      || ExpK.eval       (update              myMod         (eventToAction (actionToEvent (myact,0)))) f
  , not (ExpK.eval               (blsToKripke myScn) (preOf (eventToAction (actionToEvent (myact,0)))))
      || ExpK.eval       (update (blsToKripke myScn)        (eventToAction (actionToEvent (myact,0)))) f
  , not (SymK.evalViaBdd                      myScn  (preOf                (actionToEvent (myact,0))))
      || SymK.evalViaBdd (update              myScn                        (actionToEvent (myact,0)) ) f
  -- using dynamic operators:
  , ExpK.eval       myMod (box (Dyn "(myact,0)"               (toDyn                 (myact,0::Action))) f)
  , SymK.evalViaBdd myScn (box (Dyn "actionToEvent (myact,0)" (toDyn $ actionToEvent (myact,0::Action))) f)
  ]
  ++ case SymK.reduce (actionToEvent (myact,0)) f of
      Nothing -> []
      Just g  -> pure $ SymK.evalViaBdd (kripkeToBls myMod) (simplify g)
  ++ [ SymK.evalViaBddReduce myScn (actionToEvent (myact,0)) f ]

semanticEquivExpToSym :: PointedModel -> SimplifiedForm -> [Bool]
semanticEquivExpToSym pm (SF f) =
  [ ExpK.eval pm f
  , SymK.evalViaBdd (TransK.kripkeToBls pm) f
  ]

semanticEquivSymToExp :: BelScene -> SimplifiedForm -> [Bool]
semanticEquivSymToExp scn (SF f) =
  [ SymK.evalViaBdd scn f
  , ExpK.eval (TransK.blsToKripke scn) f
  ]

diffTest :: PointedModel -> PointedModel -> Bool
diffTest pmA pmB =
  case diffPointed pmA pmB of
    Left  b -> checkBisimPointed b pmA pmB
    Right f -> isTrue pmA f && not (isTrue pmB f)
