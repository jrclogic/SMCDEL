module Main (main) where

import Data.Dynamic (toDyn)
import Data.Map.Strict (fromList)
import Data.List (sort)
import Test.Hspec
import Test.QuickCheck
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq,set)
import SMCDEL.Language
import SMCDEL.Explicit.S5 (Action,worldsOf)
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Explicit.K as ExpK
import SMCDEL.Symbolic.K as SymK
import SMCDEL.Translations.K as TransK

main :: IO ()
main = hspec $ do
  describe "hardcoded myMod and myScn" $ do
    prop "semanticEquivalence" $ alleq . semanticEquivalenceTest
    prop "myAct and myTrf" $ \f -> (myMod `update` myAct |= f) == (myScn `update` myTrf |= f)
    prop "singleChange: random action model with change" $ \ a f -> alleq $ singleChangeTest a f
  describe "random Kripke models" $ do
    prop "Ck i -> K i" $ \(Ag i) krm f -> ExpK.eval (krm,0) (Ck [i] f `Impl` Ck [i] f)
    prop "semanticEquivExpToSym" $ \krm f -> alleq $ semanticEquivExpToSym (krm,0) f
    prop "diff" $ \krmA krmB -> diffTest (krmA,0) (krmB,0)
  describe "random belief structures" $
    prop "semanticEquivSymToExp" $ \bls f -> alleq $ semanticEquivSymToExp (bls, head (statesOf bls)) f
  describe "multipointed belief structures (all-pointed, for now)" $
    prop "semanticEquivSymToExp" $ \bls f -> alleq $ semanticEquivSymToExpMulti bls f
  prop "optimize on belief structures preserves truth" $
    \bls f -> isTrue (bls::SymK.BelStruct) f === isTrue (optimize defaultVocabulary bls) f
  modifyMaxSuccess (const 1000) $ prop "optimize on belief structures can reduce the vocabulary" $
    expectFailure (\bls -> length (vocabOf (bls :: SymK.BelStruct)) === length (vocabOf (optimize defaultVocabulary bls)))

-- | An example model with 5 agents, 5 atomic propositions and 32 worlds.
myMod :: ExpK.PointedModel
myMod = (ExpK.KrM $ fromList wlist, 0) where
  wlist = [ (w, (fromList val, fromList $ relFor val)) | (val,w) <- wvals ]
  vals  = map sort (foldl buildTable [[]] defaultVocabulary)
  wvals = zip vals [0..]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor val = [ (i, seesFrom i val) | i <- defaultAgents ]
  seesFrom i val = map snd $ filter (\(val',_) -> considers i val val') wvals
  considers :: Agent -> [(Prp,Bool)] -> [(Prp,Bool)] -> Bool
  considers "1" ps qs = ps == qs                -- knows everything
  considers "2" _  _  = False                   -- insane
  considers "3" ps qs = set ps (P 3) True == qs -- believes P 3
  considers _ _  _  = True                      -- know nothing

-- | A belief scene which is equivalent to myMod.
myScn :: SymK.BelScene
myScn = (SymK.BlS defaultVocabulary
                  (boolBddOf Top)
                  (fromList $ ("1", SymK.allsamebdd defaultVocabulary)      -- knows everything
                            : ("2", SymK.emptyRelBdd)                       -- insane
                            : ("3", relBddOfIn "3" (fst myMod))             -- believes P 3
                            : [(show i, SymK.totalRelBdd) | i<-[4,5::Int]]) -- know nothing
        , defaultVocabulary)

-- | An example Non-S5 action model with 3 events.
myAct :: ExpK.MultipointedActionModel
myAct = (ActM $ fromList
          [ (0, Act Top          (fromList [(P 1, PrpF (P 2))]) (fromList [("1",[0]),("2",[2]),("3",[2]),("4",[0,1]),("5",[0,1,2])]))
          , (1, Act (PrpF (P 1)) (fromList [(P 3, PrpF (P 4))]) (fromList [("1",[1]),("2",[2]),("3",[2]),("4",[0,1]),("5",[0,1,2])]))
          , (2, Act (PrpF (P 2)) (fromList mempty             ) (fromList [("1",[2]),("2",[2]),("3",[2]),("4",[2]  ),("5",[0,1,2])])) ]
        , [0] )

-- | A transformer which is equivalent to myAct.
-- Actions 0,1,2 are labelled with [], [P 5], [P 6] respectively.
myTrf :: SymK.MultipointedEvent
myTrf = ( Trf [P 5,P 6]
              (Conj [ Neg $ Conj [PrpF (P 5),PrpF (P 6)]
                    , PrpF (P 5) `Impl` PrpF (P 1)
                    , PrpF (P 6) `Impl` PrpF (P 2)
                    ] )
              (fromList
                [ (P 1,boolBddOf $ ite (Conj [Neg $ PrpF (P 5), Neg $ PrpF (P 6)]) (PrpF $ P 2) (PrpF $ P 1))
                , (P 3,boolBddOf $ ite (PrpF (P 5)) (PrpF $ P 4) (PrpF $ P 3))
                ] )
              (fromList
                [ ("1",SymK.allsamebdd [P 5, P 6])
                , ("2",cpBdd $ boolBddOf (PrpF (P 6)))
                , ("3",cpBdd $ boolBddOf (PrpF (P 6)))
                , ("4",SymK.allsamebdd [P 6])
                , ("5",totalRelBdd)
                ] )
        , boolBddOf $ Conj [ Neg $ PrpF (P 5), Neg $ PrpF (P 6) ] )

semanticEquivalenceTest :: SimplifiedForm -> [Bool]
semanticEquivalenceTest (SF f) =
  [ myMod |= f                     -- evaluate directly on Kripke
  , myScn |= f                     -- evaluate equivalent BDD on BlS
  , TransK.blsToKripke myScn |= f  -- evaluate on corresponding Kripke
  , TransK.kripkeToBls myMod |= f  -- evaluate on corresponding BlS
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
  , myMod |= box (Dyn "(myact,0)"               (toDyn                 (myact,0::Action))) f
  , myScn |= box (Dyn "actionToEvent (myact,0)" (toDyn $ actionToEvent (myact,0::Action))) f
  ]
  ++ case SymK.reduce (actionToEvent (myact,0)) f of
      Nothing -> []
      Just g  -> pure $ SymK.evalViaBdd (kripkeToBls myMod) (simplify g)
  ++ [ SymK.evalViaBddReduce myScn (actionToEvent (myact,0)) f ]

semanticEquivExpToSym :: PointedModel -> SimplifiedForm -> [Bool]
semanticEquivExpToSym pm (SF f) = [ pm |= f
                                  , TransK.kripkeToBls pm |= f ]

semanticEquivSymToExp :: BelScene -> SimplifiedForm -> [Bool]
semanticEquivSymToExp scn (SF f) = [ scn |= f
                                   , TransK.blsToKripke scn |= f ]

semanticEquivSymToExpMulti :: BelStruct -> SimplifiedForm -> [Bool]
semanticEquivSymToExpMulti bls (SF f) = [ bls |= f
                                        , (bls, boolBddOf Top) |= f
                                        , (krm, worldsOf krm) |= f ] where
  (krm,_) = TransK.blsToKripke (bls,undefined)

diffTest :: PointedModel -> PointedModel -> Bool
diffTest pmA pmB =
  case diffPointed pmA pmB of
    Left  b -> checkBisimPointed b pmA pmB
    Right f -> isTrue pmA f && not (isTrue pmB f)
