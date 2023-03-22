{-# LANGUAGE AllowAmbiguousTypes, FlexibleContexts, TypeApplications, ScopedTypeVariables #-}

module Main (main) where

import Data.Maybe (isJust)
import Test.Hspec
import Test.QuickCheck

import SMCDEL.Internal.Help (alleq)
import SMCDEL.Internal.MyHaskCUDD
import SMCDEL.Language
import qualified Data.Map.Strict as M
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD (Manager, makeManager, makeManagerZ)
import qualified SMCDEL.Symbolic.K as K
import qualified SMCDEL.Symbolic.K_CUDD as K_CUDD
import qualified SMCDEL.Symbolic.Ki_CUDD as Ki_CUDD
import qualified SMCDEL.Symbolic.S5 as S5
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD

main :: IO ()
main = do
  hspec $ do
    describe "CUDD / MyHaskCUDD" $ do
      before MyHaskCUDD.makeManager $
        describe "bddOnlyTests" bddOnlyTests
      before (MyHaskCUDD.makeManagerZ (length defaultVocabulary)) $ do
        describe "B O1 I1" $ cuddTests @B @O1 @I1
        describe "B O0 I1" $ cuddTests @B @O0 @I1
        describe "B O1 I0" $ cuddTests @B @O1 @I0
        describe "B O0 I0" $ cuddTests @B @O0 @I0
        describe "Z O1 I1" $ cuddTests @Z @O1 @I1
        describe "Z O0 I1" $ cuddTests @Z @O0 @I1
        describe "Z O1 I0" $ cuddTests @Z @O1 @I0
        describe "Z O0 I0" $ cuddTests @Z @O0 @I0
    describe "S5: hardcoded myKns and myKnScac" $ do
      before (MyHaskCUDD.makeManagerZ (length defaultVocabulary + 1)) $ do
        it "evalViaDd agrees for all variants" $ \mgr -> property (alleq . evalViaDdTest mgr)
        it "validViaDD agrees for all variants" $ \mgr -> property (alleq . validViaDdTest mgr)
    describe "K_CUDD: hardcoded myBlS and myBlScac" $ do
      before (MyHaskCUDD.makeManagerZ 15) $ do
        it "evalViaDd agrees for all variants" $ \mgr -> property (alleq . evalViaDdTestK mgr)
        it "validViaDD agrees for all variants" $ \mgr -> property (alleq . validViaDdTestK mgr)
    describe "Ki_CUDD: hardcoded myBlSKi" $ do
      before (MyHaskCUDD.makeManagerZ 20) $ do
        it "evalViaDd agrees for all variants" $ \mgr -> property (alleq . evalViaDdTestKi mgr)
        it "validVidaDD agrees for all variants" $ \mgr -> property (alleq . validViaDdTestKi mgr)

-- * CUDD / MyHaskCUDD

v :: [Int]
v = map fromEnum defaultVocabulary

cuddTests :: forall a b c . DdCtx a b c => SpecWith MyHaskCUDD.Manager
cuddTests = do
  describe "Basics" $ do
    it "bot == bot" $ \mgr -> (bot mgr :: Dd a b c) `shouldBe` (bot mgr :: Dd a b c)
    it "top == top" $ \mgr -> (top mgr :: Dd a b c) `shouldBe` (top mgr :: Dd a b c)
    it "top /= bot" $ \mgr -> (top mgr :: Dd a b c) `shouldNotBe` (bot mgr :: Dd a b c)
    it "bot /= top" $ \mgr -> (bot mgr :: Dd a b c) `shouldNotBe` (top mgr :: Dd a b c)
    it "neg bot == top" $ \mgr -> neg mgr (bot mgr) `shouldBe` (top mgr :: Dd a b c)
    it "neg bot /= bot" $ \mgr -> neg mgr (bot mgr) `shouldNotBe` (bot mgr :: Dd a b c)
    it "var 1 == var 1" $ \mgr -> (var mgr 1 :: Dd a b c) `shouldBe` var mgr 1
    it "var 3 /= var 2" $ \mgr -> (var mgr 3 :: Dd a b c) `shouldNotBe` var mgr 2
    it "var 1 /= var 2" $ \mgr -> (var mgr 1 :: Dd a b c) `shouldNotBe` var mgr 2
    it "var 3 == con (var 3) top" $ \mgr ->
      var mgr 3 `shouldBe` con mgr (var mgr 3) (top mgr :: Dd a b c)
    it "var 4 /= con (var 3) top" $ \mgr ->
      var mgr 4 `shouldNotBe` con mgr (var mgr 3) (top mgr :: Dd a b c)
    it "equ (var 1) (var 1) == top" $ \mgr ->
      equ mgr (var mgr 1) (var mgr 1) `shouldBe` (top mgr :: Dd a b c)
    it "exists 1 (neg $ var 1) == top" $ \mgr ->
      exists mgr 1 (neg mgr $ var mgr 1) `shouldBe` (top mgr :: Dd a b c)
    it "exists 1 (neg $ var 2) /= top" $ \mgr ->
      exists mgr 1 (neg mgr $ var mgr 2) `shouldNotBe` (top mgr :: Dd a b c)
    it "gfp (\b -> con b (var 3)) == var 3" $ \mgr ->
      gfp mgr (\b -> con mgr b (var mgr 3)) `shouldBe` (var mgr 3 :: Dd a b c)
    it "imp (conSet [var 1,var 0]) (var 1) == top" $ \mgr ->
      imp mgr (conSet mgr [var mgr 1,var mgr 0]) (var mgr 1) `shouldBe` (top mgr :: Dd a b c)
    it "imp (conSet [var 0,var 1]) (var 0) == top" $ \mgr ->
      imp mgr (conSet mgr [var mgr 0,var mgr 1]) (var mgr 0) `shouldBe` (top mgr :: Dd a b c)
    it "imp (con (var 0) (var 1)) (var 0) == top" $ \mgr ->
      imp mgr (con mgr (var mgr 0) (var mgr 1)) (var mgr 0) `shouldBe` (top mgr :: Dd a b c)
  describe "DD manipulation" $ do
    it "substitSimul" $ \mgr ->
      substitSimul mgr [(3, var mgr 4),(4, var mgr 5)] (imp mgr (var mgr 3) (var mgr 4 :: Dd a b c))
      `shouldBe`
      imp mgr (var mgr 4) (var mgr 5)
  describe "utility functions" $ do
    it "show (var 3) /= show (var 2)" $ \mgr ->
      show (var mgr 3 :: Dd a b c) `shouldNotBe` show (var mgr 2 :: Dd a b c)
    it "show (var 2) == show (var 2)" $ \mgr ->
      show (var mgr 2 :: Dd a b c) `shouldBe` show (var mgr 2 :: Dd a b c)
    it "size top is 0, 1 or 7" $ \mgr ->
      size mgr (top mgr :: Dd a b c) `elem` [0,1,7]
    it "size bot is 0, 1 or 7" $ \mgr ->
      size mgr (bot mgr :: Dd a b c) `elem` [0,1,7]
    it "size (var 2) is 2, 6 or 8" $ \mgr ->
      size mgr (var mgr 2 :: Dd a b c) `elem` [2,6,8]
    it "getDependentVars" $ \mgr ->
      getDependentVars mgr v (var mgr 2 :: Dd a b c) `shouldBe` [2]
    it "getSupport" $ \mgr ->
      getSupport mgr (var mgr 2 :: Dd a b c) `shouldSatisfy` flip elem [ [], [2] ] -- TODO: is this correct?
  describe "random tests" $ do
    it "forall exists" $ \mgr ->
      property (\(BF f) -> let (b :: Dd a b c) = S5_CUDD.boolDdOf mgr f
                           in forAll (elements [0..5]) (\n -> forall mgr n b == neg mgr (exists mgr n (neg mgr b))))
    it "restrictLaw" $ \mgr ->
      property (\(BF f) (BF g) -> let (a :: Dd a b c, b :: Dd a b c) = (S5_CUDD.boolDdOf mgr f, S5_CUDD.boolDdOf mgr g)
                                  in imp mgr b (equ mgr (restrictLaw mgr v a b) a) == (top mgr :: Dd a b c))

bddOnlyTests :: SpecWith MyHaskCUDD.Manager
bddOnlyTests = do
  it "allSats top `==` [[]]" $ \mgr -> allSats mgr (top mgr :: Dd B O1 I1) `shouldBe` [[]]
  it "anySat iff not bot" $ \mgr ->
    property (\(BF f) -> let (b :: Dd B O1 I1) = S5_CUDD.boolDdOf mgr f
                           in (b /= bot mgr) === isJust (anySat mgr b))
  it "length allSats > 0 iff not bot" $ \mgr ->
    property (\(BF f) -> let (b :: Dd B O1 I1) = S5_CUDD.boolDdOf mgr f
                           in (b /= bot mgr) ==> (length $! allSats mgr b) > 0)
  it "allSatsWith" $ \mgr ->
    property (\(BF f) -> let (b :: Dd B O1 I1) = S5_CUDD.boolDdOf mgr f
                           in all (\s -> restrictSet mgr b s == top mgr) (allSatsWith mgr (map fromEnum defaultVocabulary) b))

-- * S5_CUDD

myKnS :: (DdCtx a b c) => MyHaskCUDD.Manager -> S5_CUDD.KnowStruct a b c
myKnS mgr = S5_CUDD.KnS mgr defaultVocabulary (S5_CUDD.boolDdOf mgr Top) myDefaultObservables

myKnScac :: S5.KnowStruct
myKnScac = S5.KnS defaultVocabulary (S5.boolBddOf Top) myDefaultObservables

myDefaultObservables :: [(Agent,[Prp])]
myDefaultObservables = [("1", [P 1 .. P 4]), ("2", [P 1, P 2]), ("3", []), ("4", [P 1]), ("5", [])]

evalViaDdTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
evalViaDdTest mgr (SF f) =
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

validViaDdTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
validViaDdTest mgr (SF f) =
  [ S5.validViaBdd myKnScac f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct B O1 I1) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct B O1 I0) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct B O0 I1) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct B O0 I0) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct Z O1 I1) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct Z O1 I0) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct Z O0 I1) f
  , S5_CUDD.validViaDd (myKnS mgr :: S5_CUDD.KnowStruct Z O0 I0) f
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

evalViaDdTestK :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
evalViaDdTestK mgr (SF f) =
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

validViaDdTestK :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
validViaDdTestK mgr (SF f) =
  [ K.validViaBdd myBlScac f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct B O1 I1) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct B O1 I0) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct B O0 I1) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct B O0 I0) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct Z O1 I1) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct Z O1 I0) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct Z O0 I1) f
  , K_CUDD.validViaDd (myBlS mgr :: K_CUDD.BelStruct Z O0 I0) f
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

evalViaDdTestKi :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
evalViaDdTestKi mgr (SF f) =
  [ Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O1 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O1 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O0 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene B O0 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O1 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O1 I0) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O0 I1) f
  , Ki_CUDD.evalViaDd ((myBlSKi mgr, defaultVocabulary) :: Ki_CUDD.BelScene Z O0 I0) f
  ]

validViaDdTestKi :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
validViaDdTestKi mgr (SF f) =
  [ Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct B O1 I1) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct B O1 I0) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct B O0 I1) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct B O0 I0) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct Z O1 I1) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct Z O1 I0) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct Z O0 I1) f
  , Ki_CUDD.validViaDd (myBlSKi mgr :: Ki_CUDD.BelStruct Z O0 I0) f
  ]
