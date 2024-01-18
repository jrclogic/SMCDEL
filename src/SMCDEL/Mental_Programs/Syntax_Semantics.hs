module SMCDEL.Mental_Programs.Syntax_Semantics where
import Data.List

-- TODO: replace BoolForm with SMCDEL language:
-- import SMCDEL.Language
-- import Data.HasCacBDD -- to get "Bdd" and "con" etc.
-- see https://hackage.haskell.org/package/HasCacBDD-0.2.0.0/docs/Data-HasCacBDD.html for help :-)

type Prop = Int

-- replace with Form, or directly with BDD
data BoolForm = Topp | Bott | P Prop | Neg BoolForm | Conj BoolForm BoolForm | Disj BoolForm BoolForm | Con [BoolForm] | Dis [BoolForm] | Impl BoolForm BoolForm
    deriving (Eq,Ord,Show)

iff :: BoolForm -> BoolForm -> BoolForm
iff f g = Conj (Impl f g) (Impl g f)

satisfies :: State -> BoolForm -> Bool
satisfies _ Topp = True
satisfies _ Bott = False
satisfies s (P k) = k `elem` s
satisfies s (Neg f) = not (satisfies s f)
satisfies s (Conj f g) = (satisfies s f) && (satisfies s g)
satisfies s (Disj f g) = (satisfies s f) || (satisfies s g)
satisfies s (Con fs) = all (satisfies s) fs
satisfies s (Dis fs) = any (satisfies s) fs
satisfies s (Impl f g) = (not (satisfies s f)) || (satisfies s g)

-- Syntax of Mental Programs (corresponds to section 1 of the latex file)
data Program = Top Prop | Bot Prop | Test BoolForm | U Program Program | Seq Program Program | Ins Program Program
    deriving (Eq,Ord,Show)

type Domain = [Prop]
type State = [Prop]
type Statelaw = BoolForm
type LegitStates = [State]


allStates :: Domain -> [State]
allStates [] = [[]]
allStates (p:ps) = sort (allStates ps ++ [p:ss | ss <- allStates ps])

legitStates :: Domain -> [Statelaw] -> LegitStates
legitStates d ls = [s | s <- allStates d, all (\l -> s `satisfies` l) ls]

toSet :: Ord a => [a] -> [a]
toSet = nub . sort

-- Semantics of Mental Programs (section 2 of the latex file)
rel :: Domain -> [Statelaw] -> Program -> State -> State -> Bool
rel _ _ (Top (p)) s t = toSet t == toSet (s ++ [p])
rel _ _ (Top _) _ _ = undefined -- Wait to see if we need the more general case
rel _ _ (Bot (p)) s t = toSet t == toSet s \\ [p]
rel _ _ (Bot _) _ _ = undefined -- Same as Top
rel _ _ (Test beta) s t = toSet s == toSet t && (satisfies s beta)
rel d ss (U p1 p2) s t = rel d ss p1 s t || rel d ss p2 s t
rel d ss (Seq p1 p2) s t = any (\u -> (rel d ss p1 s u) && (rel d ss p2 u t)) (legitStates d ss ::[State])
rel d ss (Ins p1 p2) s t = rel d ss p1 s t && rel d ss p2 s t


-- Some examples:

-- This should be all true
examples1 :: [Bool]
examples1 = [rel [0,1] [Topp] (Top (0)) [1] [0,1],
             rel [0,1] [Topp] (Bot (1)) [0,1] [0],
             rel [0,1,2] [Topp] (Test (Conj (P 0) (P 1))) [0,1] [0,1],
             rel [0,1] [Topp] (U (Top (0)) (Top (1))) [0] [0,1],
             rel [0,1,2] [Dis [P 1, P 2]] (Seq (Top (2)) (Bot (1))) [1] [2],
             rel [0,1,2,3] [Neg $ P 0] (Ins (Seq (Top (3)) (Bot (2))) (Seq (Bot (2)) (Top (3)))) [1,2] [1,3]]

copy :: Prop -> Prop
copy prp = prp + 1000 -- to be replaced by cp etc. from SMCDEL.Symbolic.K

-- Translations from Mental Programs to Boolean Formulas in section 5
translate :: [Prop] -> Program -> BoolForm
translate v (Top prp) = Conj (P prp) (Con [ iff (P q) (P (copy q)) | q <- v, prp /= q ])
translate v (Bot prp) = undefined
translate v (Test f) = undefined
translate v (U b1 b2) = Disj (translate v b1) (translate v b2)
translate v (Seq b1 b2) = undefined
translate v (Ins b1 b2) = undefined

-- TODO: rename Ins to Cap
-- rename U to Cup

-- LATER: replace BoolForm with "Bdd" type :-)
-- then use "con" and "conSet"


-- I was trying to generate an infinite list of formulas given a finite vocabulary

-- generateBoolFormulas :: [Prop] -> [BoolForm]
-- generateBoolFormulas [] = []
-- generateBoolFormulas (p:props) =
--     Topp : Bott : map P (p:props) ++
--     [Neg f | f <- subFormulas] ++
--     [Conj f1 f2 | f1 <- subFormulas, f2 <- subFormulas] ++
--     [Disj f1 f2 | f1 <- subFormulas, f2 <- subFormulas] ++
--     [Impl f1 f2 | f1 <- subFormulas, f2 <- subFormulas]
--     where
--         subFormulas = generateBoolFormulas props
