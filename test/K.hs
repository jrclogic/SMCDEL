module Main (main) where

import Test.Hspec
import Test.Hspec.QuickCheck
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Explicit.S5 (Action)
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Explicit.K as ExpK
import SMCDEL.Symbolic.K as SymK
import SMCDEL.Translations.K as TransK
import Data.Map.Strict (fromList)
import Data.List (sort)

main :: IO ()
main = hspec $ do
  describe "SMCDEL.Symbolic.K" $
    prop "semantic equivalence" $ alleq . semanticEquivTest
  describe "SMCDEL.Other.Change" $
    prop "single change" $ \ a f -> alleq $ singleChangeTest a f

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

semanticEquivTest :: SimplifiedForm -> [Bool]
semanticEquivTest (SF f) =
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
  ]
  ++ case SymK.reduce (actionToEvent (myact,0)) f of
      Nothing -> []
      Just g  -> pure $ SymK.evalViaBdd (kripkeToBls myMod) (simplify g)
  ++ [ SymK.evalViaBddReduce myScn (actionToEvent (myact,0)) f ]
