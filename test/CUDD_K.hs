module Main (main) where

import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import qualified SMCDEL.Symbolic.K_CUDD as Cudd
import SMCDEL.Symbolic.K as Cac
import SMCDEL.Symbolic.S5 as CacBase
import SMCDEL.Symbolic.S5_CUDD (boolDdOf)
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD (Manager, makeManagerZ)
import SMCDEL.Internal.MyHaskCUDD
import qualified Data.Map.Strict as M

main :: IO ()
main = do
  mgr <- MyHaskCUDD.makeManagerZ 100 -- keep at 100 as BF randomises over 100 props
  hspec $ do
    describe "hardcoded myKnS" $ do
      prop "evalViaBdd agrees for all eight DD kinds" $ alleq . ddKindTest mgr
    describe "CUDD tests" $ do
      prop "restrictLaw is correct for all  " (\x y -> and $ testRestrictlaw mgr (map P [0..100]) x y)

myKnS :: (DdCtx a b c) => MyHaskCUDD.Manager -> Cudd.BelStruct a b c
myKnS mgr = Cudd.BlS mgr defaultVocabulary (boolDdOf mgr Top) (myObservables (pure . boolDdOf mgr))

myKnScac :: Cac.BelStruct
myKnScac = Cac.BlS defaultVocabulary (CacBase.boolBddOf Top) (myObservables (pure . boolBddOf))

myObservables :: (Form -> dd) -> M.Map Agent dd
myObservables formToDd = M.fromList
  [ ("1", formToDd $ Conj (zipWith Equi (map PrpF [P 2, P 4, P 6, P 8]) (map PrpF [P 3, P 5, P 7, P 9])))
  , ("2", formToDd $ Conj (zipWith Equi (map PrpF [P 2, P 4]) (map PrpF [P 3, P 5])))
  , ("3", formToDd Top)
  , ("4", formToDd $ PrpF $ P 1)
  , ("5", formToDd Bot) ]

ddKindTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTest mgr (SF f) =
  [ Cac.evalViaBdd (myKnScac, defaultVocabulary) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene B F1 S1) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene B F1 S0) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene B F0 S1) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene B F0 S0) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene Z F1 S1) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene Z F1 S0) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene Z F0 S1) f
  , Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.BelScene Z F0 S0) f
  ]

testRestrictlaw :: MyHaskCUDD.Manager -> [Prp] -> BF -> BF -> [Bool]
testRestrictlaw mgr v (BF a) (BF b) =
  [ imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd B F1 S1)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd B F0 S1)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd B F1 S0)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd B F0 S0)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd Z F1 S1)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd Z F0 S1)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd Z F1 S0)
  , imp mgr (boolDdOf mgr b) (equ mgr (restrictLaw mgr v (boolDdOf mgr a) (boolDdOf mgr b)) (boolDdOf mgr a)) == (top mgr :: Dd Z F0 S0)
  ]
