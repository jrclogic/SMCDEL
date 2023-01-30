module Main (main) where

import Test.Hspec
import Test.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Internal.MyHaskCUDD
import SMCDEL.Language
import qualified Data.Map.Strict as M
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD (Manager, makeManagerZ)
import qualified SMCDEL.Symbolic.K as K
import qualified SMCDEL.Symbolic.K_CUDD as K_CUDD
import qualified SMCDEL.Symbolic.Ki_CUDD as Ki_CUDD
import qualified SMCDEL.Symbolic.S5 as S5
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD

main :: IO ()
main = do
  hspec $ do
    describe "CUDD / MyHaskCUDD" $ do
      before (MyHaskCUDD.makeManagerZ (length defaultVocabulary + 1)) $
        it "restrictLaw for all kinds" $ \mgr -> property (\x y -> and $ testRestrictlaw mgr defaultVocabulary x y)
    describe "S5: hardcoded myKns" $ do
      before (MyHaskCUDD.makeManagerZ (length defaultVocabulary + 1)) $
        it "all DD kinds" $ \mgr -> property (alleq . ddKindTest mgr)
    describe "K_CUDD: hardcoded myBlS and myBlScac" $ do
      before (MyHaskCUDD.makeManagerZ 15) $
        it "evalViaDd agrees for all kinds" $ \mgr -> property (alleq . ddKindTestK mgr)
    describe "Ki_CUDD: hardcoded myBlSKi" $ do
      before (MyHaskCUDD.makeManagerZ 20) $
        it "evalViaDd agrees for all kinds" $ \mgr -> property (alleq . ddKindTestKi mgr)

-- * CUDD / MyHaskCUDD

-- TODO: add more, based on HasCacBDD tests!

testRestrictlaw :: MyHaskCUDD.Manager -> [Prp] -> BF -> BF -> [Bool]
testRestrictlaw mgr v (BF a) (BF b) =
  [ imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd B O1 I1)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd B O0 I1)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd B O1 I0)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd B O0 I0)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd Z O1 I1)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd Z O0 I1)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd Z O1 I0)
  , imp mgr (S5_CUDD.boolDdOf mgr b) (equ mgr (restrictLaw mgr v (S5_CUDD.boolDdOf mgr a) (S5_CUDD.boolDdOf mgr b)) (S5_CUDD.boolDdOf mgr a)) == (top mgr :: Dd Z O0 I0)
  ]

-- * S5_CUDD

myKnS :: (DdCtx a b c) => MyHaskCUDD.Manager -> S5_CUDD.KnowStruct a b c
myKnS mgr = S5_CUDD.KnS mgr defaultVocabulary (S5_CUDD.boolDdOf mgr Top) myDefaultObservables

myKnScac :: S5.KnowStruct
myKnScac = S5.KnS defaultVocabulary (S5.boolBddOf Top) myDefaultObservables

myDefaultObservables :: [(Agent,[Prp])]
myDefaultObservables = [("1", [P 1 .. P 4]), ("2", [P 1, P 2]), ("3", []), ("4", [P 1]), ("5", [])]

ddKindTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTest mgr (SF f) =
  [ S5.evalViaBdd (myKnScac, defaultVocabulary) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene B O1 I1) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene B O1 I0) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene B O0 I1) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene B O0 I0) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene Z O1 I1) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene Z O1 I0) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene Z O0 I1) f
  , S5_CUDD.evalViaDd ((myKnS mgr, defaultVocabulary) :: S5_CUDD.KnowScene Z O0 I0) f
  ]

-- * K_CUDD

myBlS :: (DdCtx a b c) => MyHaskCUDD.Manager -> K_CUDD.BelStruct a b c
myBlS mgr = K_CUDD.BlS mgr defaultVocabulary (S5_CUDD.boolDdOf mgr Top) (myObsLaws (pure . S5_CUDD.boolDdOf mgr))

myBlScac :: K.BelStruct
myBlScac = K.BlS defaultVocabulary (S5.boolBddOf Top) (myObsLaws (pure . S5.boolBddOf))

myObsLaws :: (Form -> dd) -> M.Map Agent dd
myObsLaws formToDd = M.fromList
  [ ("1", formToDd $ Conj (zipWith Equi (map PrpF [P 2, P 4, P 6, P 8]) (map PrpF [P 3, P 5, P 7, P 9])))
  , ("2", formToDd $ Conj (zipWith Equi (map PrpF [P 2, P 4]) (map PrpF [P 3, P 5])))
  , ("3", formToDd Top)
  , ("4", formToDd $ PrpF $ P 1)
  , ("5", formToDd Bot) ]

ddKindTestK :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTestK mgr (SF f) =
  [ K.evalViaBdd (myBlScac, defaultVocabulary) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene B O1 I1) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene B O1 I0) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene B O0 I1) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene B O0 I0) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene Z O1 I1) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene Z O1 I0) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene Z O0 I1) f
  , K_CUDD.evalViaDd ((myBlS mgr, defaultVocabulary) :: K_CUDD.BelScene Z O0 I0) f
  ]

-- * Ki_CUDD

myBlSKi :: (DdCtx a b c) => MyHaskCUDD.Manager -> Ki_CUDD.BelStruct a b c
myBlSKi mgr = Ki_CUDD.BlS mgr defaultVocabulary (S5_CUDD.boolDdOf mgr Top) myObs where
  myObs :: (DdCtx a b c) => (M.Map Agent Int, Ki_CUDD.RelDD a b c)
  myObs = (M.fromList [("1", 0), ("2", 1), ("3", 2), ("4", 3), ("5", 4)], pure $ S5_CUDD.boolDdOf mgr $ Conj
    [ Impl (PrpF $ P 0) (Conj (zipWith Equi (map PrpF [P 5, P 7, P 9, P 11]) (map PrpF [P 6, P 8, P 10, P 12])))
    , Impl (PrpF $ P 1) (Conj (zipWith Equi (map PrpF [P 5, P 7]) (map PrpF [P 6, P 8])))
    , Impl (PrpF $ P 2) Bot
    , Impl (PrpF $ P 3) (PrpF $ P 5)
    , Impl (PrpF $ P 4) Top
    ])

ddKindTestKi :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTestKi mgr (SF f) =
  [ Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O1 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O1 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O0 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O0 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O1 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O1 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O0 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O0 I0) f
  ]
