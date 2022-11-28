module Main (main) where

import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as Cudd
import SMCDEL.Symbolic.S5 as Cac
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD (Manager, makeManagerZ)
import SMCDEL.Internal.MyHaskCUDD (Z, B, F0, F1, S0, S1, DdCtx)

main :: IO ()
main = do
  mgr <- MyHaskCUDD.makeManagerZ 15
  hspec $ do
    describe "hardcoded myScn" $ do
      prop "all DD kinds" $ alleq . ddKindTest mgr

myKnS :: (DdCtx a b c) => MyHaskCUDD.Manager -> Cudd.KnowStruct a b c
myKnS mgr = Cudd.KnS mgr defaultVocabulary (Cudd.boolDdOf mgr Top) myDefaultObservables

myKnScac :: Cac.KnowStruct
myKnScac = Cac.KnS defaultVocabulary (Cac.boolBddOf Top) myDefaultObservables

myDefaultObservables :: [(Agent,[Prp])]
myDefaultObservables = [("1", [P 1 .. P 4]), ("2", [P 1, P 2]), ("3", []), ("4", [P 1]), ("5", [])]

ddKindTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTest mgr (SF f) =
  [
    Cac.evalViaBdd (myKnScac, defaultVocabulary) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene B F1 S1) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene B F1 S0) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene B F0 S1) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene B F0 S0) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene Z F1 S1) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene Z F1 S0) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene Z F0 S1) f,
    Cudd.evalViaDd ((myKnS mgr, defaultVocabulary) :: Cudd.KnowScene Z F0 S0) f
  ]
