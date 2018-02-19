module Main where

import Data.List
import Test.Hspec
import Test.Hspec.QuickCheck
import SMCDEL.Examples
import SMCDEL.Examples.DiningCrypto
import SMCDEL.Examples.DrinkLogic
import SMCDEL.Examples.MuddyChildren
import SMCDEL.Examples.RussianCards
import SMCDEL.Examples.SumAndProduct
import SMCDEL.Examples.WhatSum
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5
import qualified SMCDEL.Explicit.S5 as Exp
import qualified SMCDEL.Symbolic.K as SymK
import qualified SMCDEL.Explicit.K as ExpK

main :: IO ()
main = hspec $ do
  describe "SMCDEL.Language" $ do
    prop "freshp returns a fresh proposition" $
      \props -> freshp props `notElem` props
    prop "simplifying a boolean formula yields something equivalent" $
      \(BF bf) -> boolBddOf bf == boolBddOf (simplify bf)
    prop "simplifying a boolean formula only removes propositions" $
      \(BF bf) -> all (`elem` propsInForm bf) (propsInForm (simplify bf))
    prop "list of subformulas is already nubbed" $
      \f -> nub (subformulas f) == subformulas f
    prop "formulas are identical iff their show strings are" $
      \f g -> ((f::Form) == g) == (show f == show g)
    prop "boolean formulas with same prettyprint are equivalent" $
      \(BF bf) (BF bg) -> (ppForm bf /= ppForm bg) || boolBddOf bf == boolBddOf bg
    prop "boolean formulas with same LaTeX are equivalent" $
      \(BF bf) (BF bg) -> (tex bf /= tex bg) || boolBddOf bf == boolBddOf bg
    it "we can LaTeX the testForm" $ tex testForm == intercalate "\n"
        [ " \\forall \\{ p_{3} \\} ( \\bigvee \\{"
        , " \\bot , p_{3} ,\\bot \\} \\leftrightarrow \\bigwedge \\{"
        , "\\top , ( \\top \\oplus K^?_{\\text{Alice}} p_{4} ) ,[Alice,Bob?! p_{5} ] K^?_{\\text{Bob}} p_{5} \\} ) " ]
  describe "SMCDEL.Symbolic.S5" $
    prop "boolEvalViaBdd agrees on simplified formulas" $
      \(BF bf) props -> let truths = nub props in
        boolEvalViaBdd truths bf == boolEvalViaBdd truths (simplify bf)
  describe "SMCDEL.Other.BDD2Form" $ do
    prop "boolBddOf . formOf . boolBddOf == boolBddOf" $
      \(BF bf) -> (boolBddOf . formOf . boolBddOf) bf == boolBddOf bf
    prop "boolBddOf . formOf == id" $
      \b -> b == boolBddOf (formOf b)
    prop "boolBddOf (Equi bf (formOf (boolBddOf bf))) == boolBddOf Top" $
      \(BF bf) -> boolBddOf (Equi bf (formOf (boolBddOf bf))) == boolBddOf Top
  describe "SMCDEL.Explicit.S5" $
    prop "generatedSubmodel preserves truth" $
      \m f -> Exp.eval (m, head $ Exp.worldsOf m) f == Exp.eval (Exp.generatedSubmodel (m, head $ Exp.worldsOf m)) f
  describe "SMCDEL.Examples" $ do
    it "modelA: bob knows p, alice does not" $
      Exp.eval modelA $ Conj [K bob (PrpF (P 0)), Neg $ K alice (PrpF (P 0))]
    it "modelB: bob knows p, alice does not know whether he knows whether p" $
      Exp.eval modelB $ Conj [K bob (PrpF (P 0)), Neg $ Kw alice (Kw bob (PrpF (P 0)))]
    it "knsA has two states while knsB has three" $
      [2,3] == map (length . statesOf . fst) [knsA,knsB]
    it "redundantModel and minimizedModel are bisimilar" $
      Exp.checkBisim
        [(0,0),(1,0),(2,1)]
        (fst redundantModel)
        (fst minimizedModel `Exp.withoutProps` [P 2])
    it "findStateMap works for modelB and knsB" $
      let (Just g) = findStateMap modelB knsB in equivalentWith modelB knsB g
    it "findStateMap works for redundantModel and myKNS" $
      let (Just g) = findStateMap redundantModel myKNS in equivalentWith redundantModel myKNS g
    it "findStateMap works for minimizedModel and myKNS" $
      let (Just g) = findStateMap minimizedModel myKNS in equivalentWith minimizedModel myKNS g
    it "Three Muddy Children" $
      evalViaBdd mudScn0 (nobodyknows 3) &&
      evalViaBdd mudScn1 (nobodyknows 3) &&
      evalViaBdd mudScn2 (Conj [knows i | i <- [1..3]]) &&
      length (SMCDEL.Symbolic.S5.statesOf mudKns2) == 1
    it "Thirsty Logicians: valid for up to 10 agents" $
      all thirstyCheck [3..10]
    it "Dining Crypto: valid for up to 9 agents" $
      dcValid && all genDcValid [3..9]
    it "Dining Crypto, dcScn2: Only Alice knows that she paid:" $
      evalViaBdd dcScn2 $
        Conj [K "1" (PrpF (P 1)), Neg $ K "2" (PrpF (P 1)), Neg $ K "3" (PrpF (P 1))]
    it "Russian Cards: all checks"
      SMCDEL.Examples.RussianCards.rcAllChecks
    it "Russian Cards: 102 solutions" $
      length (filter checkSet allHandLists) == 102
    it "Sum and Product: There is exactly one solution." $
      length sapSolutions == 1
    it "Sum and Product: (4,13) is a solution." $
      validViaBdd sapKnStruct (Impl (Conj [xIs 4, yIs 13]) sapProtocol)
    it "Sum and Product: (4,13) is the only solution." $
      validViaBdd sapKnStruct (Impl sapProtocol (Conj [xIs 4, yIs 13]))
    it "What Sum: There are 330 solutions." $
      length SMCDEL.Examples.WhatSum.wsSolutions == 330
  let ags = map show [1::Int,2,3]
  describe "SMCDEL.Explicit.K" $ do
    it "3MC genKrp: Top is Ck and Bot is not Ck" $
      ExpK.eval ExpK.myMudGenKrpInit $ Conj [Ck ags Top, Neg (Ck ags Bot)]
    it "3MC genKrp: It is not common knowledge that someone is muddy" $
      ExpK.eval ExpK.myMudGenKrpInit $
        Neg $ Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3])
    it "3MC genKrp: after announcing makes it common knowledge that someone is muddy" $
      ExpK.eval ExpK.myMudGenKrpInit $
        PubAnnounce (Disj (map (PrpF . P) [1,2,3])) $ Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3])
  describe "SMCDEL.Symbolic.K" $ do
    it "3MC genScn: Top is Ck and Bot is not Ck" $
      SymK.evalViaBdd SMCDEL.Examples.MuddyChildren.myMudBelScnInit $ Conj [Ck ags Top, Neg (Ck ags Bot)]
    it "3MC genScn: It is not common knowledge that someone is muddy" $
      SymK.evalViaBdd SMCDEL.Examples.MuddyChildren.myMudBelScnInit $
        Neg $ Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3])
    it "3MC genScn: after announcing makes it common knowledge that someone is muddy" $
      SymK.evalViaBdd SMCDEL.Examples.MuddyChildren.myMudBelScnInit $
        PubAnnounce (Disj (map (PrpF . P) [1,2,3])) $ Ck (map show [1::Int,2,3]) $ Disj (map (PrpF . P) [1,2,3])
