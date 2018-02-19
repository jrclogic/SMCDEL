module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Explicit.K as ExpK
import SMCDEL.Symbolic.K as SymK
import SMCDEL.Translations.K as TransK
import SMCDEL.Explicit.K.Change
import SMCDEL.Symbolic.K.Change
import SMCDEL.Translations.K.Change
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

singleChangeTest :: ChangeModel -> SimplifiedForm -> [Bool]
singleChangeTest myact (SF f) = [a,b,c,d,e] ++ h where
  a = ExpK.eval       (productChange              myMod                                 (myact,0)  ) f
  b = SymK.evalViaBdd (transform     (kripkeToBls myMod)                 (actionToEvent (myact,0)) ) f
  c = ExpK.eval       (productChange              myMod  (eventToAction' (actionToEvent (myact,0)))) f
  d = ExpK.eval       (productChange (blsToKripke myScn) (eventToAction' (actionToEvent (myact,0)))) f
  e = SymK.evalViaBdd (transform                  myScn                  (actionToEvent (myact,0)) ) f
  h = case SMCDEL.Symbolic.K.Change.reduce (actionToEvent (myact,0)) f of
    Nothing -> []
    Just g  -> pure $ SymK.evalViaBdd (kripkeToBls myMod) (simplify g)
