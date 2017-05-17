
module Main where

import Data.List
import Test.Hspec
import Test.QuickCheck
import SMCDEL.Examples
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.HasCacBDD
import qualified SMCDEL.Explicit.Simple

main :: IO ()
main = hspec $ do
  describe "SMCDEL.Language" $ do
    it "freshp returns a fresh proposition" $
      property $ \props -> freshp props `notElem` props
    it "simplifying a boolean formula yields something equivalent" $
      property $ \(BF bf) -> boolBddOf bf == boolBddOf (simplify bf)
    it "simplifying a boolean formula only removes propositions" $
      property $ \(BF bf) -> all (`elem` propsInForm bf) (propsInForm (simplify bf))
    it "list of subformulas is already nubbed" $
      property $ \f -> nub (subformulas f) == subformulas f
    it "formulas are identical iff their show strings are" $
      property $ \f g -> ((f::Form) == g) == (show f == show g)
    it "boolean formulas with same prettyprint are equivalent" $
      property $ \(BF bf) (BF bg) -> (ppForm bf /= ppForm bg) || boolBddOf bf == boolBddOf bg
    it "boolean formulas with same LaTeX are equivalent" $
      property $ \(BF bf) (BF bg) -> (tex bf /= tex bg) || boolBddOf bf == boolBddOf bg
    it "we can LaTeX the testForm" $ tex testForm == intercalate "\n"
        [ " \\forall \\{ p_{3} \\}  ( \\bigvee \\{"
        , " \\bot , p_{3} ,\\bot  \\}  \\leftrightarrow \\bigwedge \\{"
        , "\\top , ( \\top  \\oplus K^?_{\\text{Alice}}  p_{4}  ) ,[Alice,Bob?! p_{5} ] K^?_{\\text{Bob}}  p_{5}  \\}  ) " ]
  describe "SMCDEL.Symbolic.HasCacBDD" $
    it "boolEvalViaBdd agrees on simplified formulas" $
      property $ \(BF bf) props -> let truths = nub props in boolEvalViaBdd truths bf == boolEvalViaBdd truths (simplify bf)
  describe "SMCDEL.Other.BDD2Form" $
    it "boolBddOf . formOf . boolBddOf == boolBddOf" $
      property $ \(BF bf) -> (boolBddOf . formOf . boolBddOf) bf == boolBddOf bf
  describe "SMCDEL.Examples" $ do
    it "modelA: bob knows p, alice does not" $
      SMCDEL.Explicit.Simple.eval modelA $ Conj [K bob (PrpF (P 0)), Neg $ K alice (PrpF (P 0))]
    it "modelB: bob knows p, alice does not know whether he knows whether p" $
      SMCDEL.Explicit.Simple.eval modelB $ Conj [K bob (PrpF (P 0)), Neg $ Kw alice (Kw bob (PrpF (P 0)))]
    it "knsA has two states while knsB has three" $
      [2,3] == map (length . statesOf . fst) [knsA,knsB]
    it "Three Muddy Children" $
      evalViaBdd mudScn0 (nobodyknows 3) &&
      evalViaBdd mudScn1 (nobodyknows 3) &&
      evalViaBdd mudScn2 (Conj [knows i | i <- [1..3]]) &&
      length (SMCDEL.Symbolic.HasCacBDD.statesOf mudKns2) == 1
    it "Thirsty Logicians: valid for up to 10 agents" $
      all thirstyCheck [3..10]
    it "Dining Crypto: valid for up to 9 agents" $
      dcValid && all genDcValid [3..9]
    it "Dining Crypto, dcScn2: It is only known to Alice whether she paid:" $
      evalViaBdd dcScn2 (K "1" (PrpF (P 1))) &&
      not (evalViaBdd dcScn2 (K "2" (PrpF (P 1)))) &&
      not (evalViaBdd dcScn2 (K "3" (PrpF (P 1))))
    it "Russian Cards: all checks"
      SMCDEL.Examples.rcAllChecks
    it "Russian Cards: 102 solutions" $
      length (filter checkSet allHandLists) == 102
    it "Sum and Product: There is exactly one solution." $
      length sapSolutions == 1
    it "Sum and Product: (4,13) is a solution." $
      validViaBdd sapKnStruct (Impl (Conj [xIs 4, yIs 13]) sapProtocol)
    it "Sum and Product: (4,13) is the only solution." $
      validViaBdd sapKnStruct (Impl sapProtocol (Conj [xIs 4, yIs 13]))
    it "What Sum: 330 solutions" $
      length (nub $ map wsExplainState wsSolutions) == 330
