module SMCDEL.Mental_Programs.Syntax_Semantics where
import Data.List

import SMCDEL.Language
import Data.HasCacBDD -- to get "Bdd" and "con" etc.
import SMCDEL.Internal.Help (seteq)
import SMCDEL.Symbolic.S5 (bddEval, boolBddOf)
import SMCDEL.Symbolic.K (RelBDD, mvBdd, allsamebdd)

-- replace with Form, or directly with BDD
-- data BoolForm = Topp | Bott | P Prop | Neg BoolForm | Conj BoolForm BoolForm | Disj BoolForm BoolForm | Con [BoolForm] | Dis [BoolForm] | Impl BoolForm BoolForm
--     deriving (Eq,Ord,Show)


-- Syntax of Mental Programs (corresponds to section 1 of the latex file)
data Program = SetTrue Prp | SetFalse Prp | Test Bdd | U Program Program | Seq Program Program | Ins Program Program
    deriving (Eq,Show)

type State = [Prp]
type LegitStates = [State]

run :: Program -> State -> [State]
run = undefined

-- Semantics of Mental Programs (section 2 of the latex file)
rel :: Program -> State -> State -> Bool
rel (SetTrue p) s t = t `seteq` (s ++ [p])
rel (SetFalse p) s t = t `seteq` (s \\ [p])
rel (Test beta) s t = s `seteq` t && bddEval s beta
rel (U p1 p2) s t = rel p1 s t || rel p2 s t
rel (Seq p1 p2) s t = any (\u -> rel p1 s u && rel p2 u t) (undefined :: [State]) -- how did Maickel do this?
rel (Ins p1 p2) s t = rel p1 s t && rel p2 s t


-- More general Semantics of Mental Programs, given a domain

allStates :: [Prp] -> [State]
allStates [] = [[]]
allStates (p:ps) = sort (allStates ps ++ [p:ss | ss <- allStates ps])

legitStates :: [Prp] -> Bdd -> LegitStates
legitStates d theta = [s | s <- allStates d, s `bddEval` theta]

toSet :: Ord a => [a] -> [a]
toSet = nub . sort

rel' :: [Prp] -> Bdd -> Program -> State -> State -> Bool
rel' _ _ (SetTrue p) s t = toSet t == toSet (s ++ [p])
rel' _ _ (SetFalse p) s t = toSet t == toSet s \\ [p]
rel' _ _ (Test beta) s t = toSet s == toSet t && bddEval s beta
rel' d theta (U p1 p2) s t = rel' d theta p1 s t || rel' d theta p2 s t
rel' d theta (Seq p1 p2) s t = any (\u -> rel' d theta p1 s u && rel' d theta p2 u t) (legitStates d theta ::[State])
rel' d theta (Ins p1 p2) s t = rel' d theta p1 s t && rel' d theta p2 s t


-- Some examples:

-- This should be all true
examples1 :: [Bool]
examples1 = [rel' [P 0, P 1] top (SetTrue (P 0)) [P 1] [P 0, P 1],
             rel' [P 0, P 1] top (SetFalse (P 1)) [P 0, P 1] [P 0],
             rel' [P 0, P 1, P 2] top (Test (boolBddOf $ Conj [ PrpF (P 0), PrpF (P 1)])) [P 0, P 1] [P 0, P 1],
             rel' [P 0, P 1] top (U (SetTrue (P 0)) (SetTrue (P 1))) [P 0] [P 0, P 1],
             rel' [P 0, P 1, P 2] (boolBddOf $ Disj (map (PrpF . P) [1, 2])) (Seq (SetTrue (P 2)) (SetFalse (P 1))) [P 1] [P 2],
             rel' [P 0, P 1, P 2, P 3] (boolBddOf $ Neg $ PrpF $ P 0) (Ins (Seq (SetTrue (P 3)) (SetFalse (P 2))) (Seq (SetFalse (P 2)) (SetTrue (P 3)))) [P 1, P 2] [P 1, P 3]]

-- Translations from Mental Programs to Boolean Formulas in section 5
-- RelBDD here is a BDD in the duplicate vocabulary!
translate :: [Prp] -> Program -> RelBDD
translate v (SetTrue prp) = con <$> mvBdd (boolBddOf (PrpF prp)) <*> allsamebdd (v \\ [prp])
translate v (SetFalse prp) = undefined
translate v (Test f) = undefined
translate v (U b1 b2) = dis <$> translate v b1 <*> translate v b2
translate v (Seq b1 b2) = undefined
translate v (Ins b1 b2) = undefined

-- TODO:
-- rename Ins to Cap
-- rename U to Cup
