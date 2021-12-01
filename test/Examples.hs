module Main (main) where

import Data.List
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck (expectFailure,(===))

import SMCDEL.Examples
import SMCDEL.Examples.DiningCrypto
import SMCDEL.Examples.DrinkLogic
import SMCDEL.Examples.MuddyChildren
import SMCDEL.Examples.DoorMat
import SMCDEL.Examples.Prisoners
import SMCDEL.Examples.RussianCards
import SMCDEL.Examples.SumAndProduct
import SMCDEL.Examples.WhatSum
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.BDD2Form
import SMCDEL.Other.Planning
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5
import qualified SMCDEL.Explicit.S5 as Exp
import qualified SMCDEL.Internal.MyHaskCUDD
import qualified SMCDEL.Symbolic.S5_CUDD
import qualified Data.HasCacBDD

main :: IO ()
main = hspec $ do
  describe "SMCDEL.Language" $ do
    prop "freshp returns a fresh proposition" $
      \props -> freshp props `notElem` props
    prop "simplifying a boolean formula yields something equivalent" $
      \(BF bf) -> boolBddOf bf === boolBddOf (simplify bf)
    prop "simplifying a boolean formula only removes propositions" $
      \(BF bf) -> all (`elem` propsInForm bf) (propsInForm (simplify bf))
    prop "list of subformulas is already nubbed" $
      \f -> nub (subformulas f) === subformulas f
    prop "formulas are identical iff their show strings are" $
      \f g -> ((f::Form) == g) === (show f == show g)
    prop "boolean formulas with same prettyprint are equivalent" $
      \(BF bf) (BF bg) -> (ppForm bf /= ppForm bg) || boolBddOf bf == boolBddOf bg
    prop "boolean formulas with same LaTeX are equivalent" $
      \(BF bf) (BF bg) -> (tex bf /= tex bg) || boolBddOf bf == boolBddOf bg
    it "we can LaTeX the testForm" $ tex testForm === intercalate "\n"
        [ " \\forall \\{ p_{3} \\} ( \\bigvee \\{"
        , " \\bot , p_{3} ,\\bot \\} \\leftrightarrow \\bigwedge \\{"
        , "\\top , ( \\top \\oplus K^?_{\\text{Alice}} p_{4} ) ,[Alice,Bob?! p_{5} ] K^?_{\\text{Bob}} p_{5} \\} ) " ]
    it "svgViaTex works for modelA" $
        isInfixOf "stroke-linecap:butt" (svgViaTex modelA)
    prop "svgViaTex can yield strings of different length" $
      expectFailure (\m1 m2 ->
            length (svgViaTex (m1::Exp.KripkeModelS5,0::Exp.World))
        === length (svgViaTex (m2::Exp.KripkeModelS5,0::Exp.World)) )
  describe "SMCDEL.Symbolic.S5" $ do
    prop "boolEvalViaBdd agrees on simplified formulas" $
      \(BF bf) props -> let truths = nub props in
        boolEvalViaBdd truths bf === boolEvalViaBdd truths (simplify bf)
    prop "optimize preserves truth" $
      \kns f -> let scene = (kns :: KnowStruct, head $ statesOf kns)
                in isTrue scene f === isTrue (optimize defaultVocabulary scene) f
    prop "generatedSubstructure preserves truth" $
      \kns f -> let scene = (kns :: KnowStruct, booloutof (head $ statesOf kns) (vocabOf kns) )
                in isTrue scene f === isTrue (generatedSubstructure scene) f
    modifyMaxSuccess (const 1000) $ prop "optimize can reduce the vocabulary" $
      expectFailure (\kns -> length (vocabOf (kns :: KnowStruct)) == length (vocabOf (optimize defaultVocabulary kns)))
  describe "SMCDEL.Symbolic.S5_CUDD and SMCDEL.Internal.MyHaskCUDD" $ do
    it "gfp (\b -> con b (var 3)) == var 3" $ SMCDEL.Internal.MyHaskCUDD.gfp (\b -> SMCDEL.Internal.MyHaskCUDD.con b (SMCDEL.Internal.MyHaskCUDD.var 3)) `shouldBe` SMCDEL.Internal.MyHaskCUDD.var 3
    it "exists 1 (neg $ var 1) == top" $ SMCDEL.Internal.MyHaskCUDD.exists 1 (SMCDEL.Internal.MyHaskCUDD.neg $ SMCDEL.Internal.MyHaskCUDD.var 1) `shouldBe` SMCDEL.Internal.MyHaskCUDD.top
    it "exists 1 (neg $ var 2) /= top" $ SMCDEL.Internal.MyHaskCUDD.exists 1 (SMCDEL.Internal.MyHaskCUDD.neg $ SMCDEL.Internal.MyHaskCUDD.var 2) `shouldNotBe` SMCDEL.Internal.MyHaskCUDD.top
    it "forall 1 (neg $ var 1) == bot" $ SMCDEL.Internal.MyHaskCUDD.forall 1 (SMCDEL.Internal.MyHaskCUDD.neg $ SMCDEL.Internal.MyHaskCUDD.var 1) `shouldBe` SMCDEL.Internal.MyHaskCUDD.bot
    it "forall 1 (neg $ var 2) /= bot" $ SMCDEL.Internal.MyHaskCUDD.forall 1 (SMCDEL.Internal.MyHaskCUDD.neg $ SMCDEL.Internal.MyHaskCUDD.var 2) `shouldNotBe` SMCDEL.Internal.MyHaskCUDD.bot
    prop "HasCacBDD and CUDD give same allSats" $
      \(BF bf) -> sort (Data.HasCacBDD.allSats (boolBddOf bf)) === sort (SMCDEL.Internal.MyHaskCUDD.allSats (SMCDEL.Symbolic.S5_CUDD.boolBddOf bf))
    prop "HasCacBDD and CUDD give same anySat" $
      \(BF bf) -> Data.HasCacBDD.anySat (boolBddOf bf) === SMCDEL.Internal.MyHaskCUDD.anySat (SMCDEL.Symbolic.S5_CUDD.boolBddOf bf)
  describe "SMCDEL.Other.BDD2Form" $ do
    prop "boolBddOf . formOf == id" $
      \b -> b === boolBddOf (formOf b)
    prop "boolBddOf (Equi bf (formOf (boolBddOf bf))) == boolBddOf Top" $
      \(BF bf) -> boolBddOf (Equi bf (formOf (boolBddOf bf))) === boolBddOf Top
  describe "SMCDEL.Explicit.S5" $ do
    prop "generatedSubmodel preserves truth" $
      \m f -> let pm = (m::Exp.KripkeModelS5, head $ Exp.worldsOf m)
              in isTrue pm f === isTrue (Exp.generatedSubmodel pm) f
    prop "optimize preserves truth" $
      \m f -> let pm = (m::Exp.KripkeModelS5, head $ Exp.worldsOf m)
              in isTrue pm f === isTrue (optimize (vocabOf m) pm) f
    prop "optimize can shrink the model" $
      expectFailure (\m -> let pm = (m::Exp.KripkeModelS5, head $ Exp.worldsOf m)
                           in length (Exp.worldsOf pm) <= length (Exp.worldsOf (optimize (vocabOf m) pm)) )
  describe "SMCDEL.Examples" $ do
    it "modelA: bob knows p, alice does not" $
      modelA |= Conj [K bob (PrpF (P 0)), Neg $ K alice (PrpF (P 0))]
    it "modelB: bob knows p, alice does not know whether he knows whether p" $
      modelB |= Conj [K bob (PrpF (P 0)), Neg $ Kw alice (Kw bob (PrpF (P 0)))]
    it "knsA has two states while knsB has three" $
      [2,3] === map (length . statesOf . fst) [knsA,knsB]
    it "redundantModel and minimizedModel are bisimilar" $
      Exp.checkBisim
        [(0,0),(1,0),(2,1)]
        (fst redundantModel)
        (fst minimizedModel `Exp.withoutProps` [P 2])
    it "bisiminimizing redundantModel removes world 0" $
      Exp.bisiminimize redundantModel === (fst redundantModel `Exp.withoutWorld` 0, 1)
    it "findStateMap works for modelB and knsB" $
      let (Just g) = findStateMap modelB knsB in equivalentWith modelB knsB g
    it "findStateMap works for redundantModel and myKNS" $
      let (Just g) = findStateMap redundantModel myKNS in equivalentWith redundantModel myKNS g
    it "findStateMap works for minimizedModel and myKNS" $
      let (Just g) = findStateMap minimizedModel myKNS in equivalentWith minimizedModel myKNS g
    it "checkPropu myPropu (fst myKNS) (fst minimizedKNS) (vocabOf myKNS)" $
      checkPropu myPropu (fst myKNS) (fst minimizedKNS) (vocabOf myKNS)
    describe "SMCDEL.Examples.MuddyChildren" $ do
      it "mudScn0: nobodyknows 3" $ mudScn0 |= nobodyknows 3
      it "mudScn1: nobodyknows 3" $ mudScn1 |= nobodyknows 3
      it "mudScn2: everyone knows" $ mudScn2 |= Conj [knows i | i <- [1..3]]
      it "mudKns2 has one state" $ length (SMCDEL.Symbolic.S5.statesOf mudKns2) === 1
      it "build result == mudScnInit 3 3" $ buildResult === mudScnInit 3 3
    it "Thirsty Logicians: valid for up to 10 agents" $
      all thirstyCheck [3..10]
    it "Dining Crypto: valid for up to 9 agents" $
      dcValid && all genDcValid [3..9]
    it "Dining Crypto, dcScn2: Only Alice knows that she paid:" $
      dcScn2 |= Conj [ K "1" (PrpF (P 1))
                     , Neg $ K "2" (PrpF (P 1))
                     , Neg $ K "3" (PrpF (P 1)) ]
    describe "SMCDEL.Examples.DoorMat" $ do
      it "tryTake reaches the goal" $
        reachesOn (Do "tryTake" tryTake (Check dmGoal Stop)) dmGoal dmStart
      it "the plan found with 'findPlan 3' works" $
        reachesOn (head $ findPlan 3 dm) dmGoal dmStart
      it "tryTake is not an IC plan" $
        not $ [("Bob",tryTakeL)] `icSolves` dmCoop
      it "dmPlan2 `icSolves` dmCoop2" $
          dmPlan2 `icSolves` dmCoop2
    it "Three Prisoners: Explicit Version reaches the goal" $
      endOf prisonExpStory `isTrue` prisonGoal
    it "Three Prisoners: Symbolic Version reaches the goal" $
      endOf prisonSymStory `isTrue` prisonGoal
    describe "SMCDEL.Examples.RussianCards" $ do
      it "rcAllChecks"
        SMCDEL.Examples.RussianCards.rcAllChecks
      it "there are 102 safe hands" $
        length safeHandLists === 102
      it "there are 102 solutions" $
        length (filter checkSet allHandLists) === 102
      it "rusSCNfor (3,3,1) == rusSCN" $
        rusSCNfor (3,3,1) === rusSCN
      it "head rcSolutionsViaPlanning == head rcSolutions" $
        head rcSolutionsViaPlanning === head rcSolutions
      it "reachesOn rcPlan rcGoal rusSCN" $
        reachesOn rcPlan rcGoal rusSCN
    it "Sum and Product: There is exactly one solution." $
      length sapSolutions === 1
    it "Sum and Product: (4,13) is a solution." $
      sapKnStruct |= Impl (Conj [xIs 4, yIs 13]) sapProtocol
    it "Sum and Product: (4,13) is the only solution." $
      sapKnStruct |= Impl sapProtocol (Conj [xIs 4, yIs 13])
    it "Sum and Product: explaining the solution." $
      map sapExplainState sapSolutions `shouldBe` ["x = 4, y = 13, x+y = 17 and x*y = 52"]
    it "What Sum: There are 330 solutions." $
      length SMCDEL.Examples.WhatSum.wsSolutions === 330
    it "What Sum: The first solution is [('a',1),('b',3),('c',2)]" $
      wsExplainState (head wsSolutions) `shouldBe` [('a',1),('b',3),('c',2)]
  let ags = agentsOf myMudGenKrpInit
  describe "SMCDEL.Explicit.K" $ do
    it "3MC genKrp: Top is Ck and Bot is not Ck" $
      myMudGenKrpInit |= Conj [Ck ags Top, Neg (Ck ags Bot)]
    it "3MC genKrp: It is not common knowledge that someone is muddy" $
      myMudGenKrpInit |= Neg (Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3]))
    it "3MC genKrp: after announcing makes it common knowledge that someone is muddy" $
      myMudGenKrpInit |= PubAnnounce (Disj (map (PrpF . P) [1,2,3])) (Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3]))
  describe "SMCDEL.Symbolic.K" $ do
    it "3MC genScn: Top is Ck and Bot is not Ck" $
      SMCDEL.Examples.MuddyChildren.myMudBelScnInit |= Conj [Ck ags Top, Neg (Ck ags Bot)]
    it "3MC genScn: It is not common knowledge that someone is muddy" $
      SMCDEL.Examples.MuddyChildren.myMudBelScnInit |=
        Neg (Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3]))
    it "3MC genScn: after announcing makes it common knowledge that someone is muddy" $
      SMCDEL.Examples.MuddyChildren.myMudBelScnInit |=
        PubAnnounce (Disj (map (PrpF . P) [1,2,3])) (Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3]))
