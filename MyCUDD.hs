module MyCUDD (
  -- * Types
  Bdd, Assignment,
  -- * Creation of new BDDs
  top, bot, var,
  -- * Combination and Manipulation of BDDs
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  exists, forall, forallSet, existsSet,
  restrict, restrictSet, restrictLaw,
  ifthenelse, gfp, relabel,
  -- * Get satisfying assignments
  allSats, allSatsWith, satCountWith, anySat,
  -- * Show and convert to trees
  showGraph, genGraph, maxVarOf
) where

import Data.List
import Data.Maybe (fromJust)
import System.Process
import System.IO
import qualified Data.Boolean.CUDD

type Bdd = Data.Boolean.CUDD.BDD

top :: Bdd
top = Data.Boolean.CUDD.true

bot :: Bdd
bot = Data.Boolean.CUDD.false

var :: Int -> Bdd
var n = Data.Boolean.CUDD.bvar (show n)

neg :: Bdd -> Bdd
neg = Data.Boolean.CUDD.neg

xor :: Bdd -> Bdd -> Bdd
xor = Data.Boolean.CUDD.xor

exists :: Int -> Bdd -> Bdd
exists n = Data.Boolean.CUDD.exists (Data.Boolean.CUDD.mkGroup [var n])

forall :: Int -> Bdd -> Bdd
forall n = Data.Boolean.CUDD.forall (Data.Boolean.CUDD.mkGroup [var n])

existsSet :: [Int] -> Bdd -> Bdd
existsSet ns = Data.Boolean.CUDD.exists (Data.Boolean.CUDD.mkGroup (map var ns))

forallSet :: [Int] -> Bdd -> Bdd
forallSet ns = Data.Boolean.CUDD.forall (Data.Boolean.CUDD.mkGroup (map var ns))

equ :: Bdd -> Bdd -> Bdd
equ = (Data.Boolean.CUDD.<->)

imp :: Bdd -> Bdd -> Bdd
imp = (Data.Boolean.CUDD.-->)

con :: Bdd -> Bdd -> Bdd
con = (Data.Boolean.CUDD./\)

dis :: Bdd -> Bdd -> Bdd
dis = (Data.Boolean.CUDD.\/)

conSet :: [Bdd] -> Bdd
conSet = Data.Boolean.CUDD.conjoin

disSet :: [Bdd] -> Bdd
disSet = Data.Boolean.CUDD.disjoin

xorSet :: [Bdd] -> Bdd
xorSet [] = bot
xorSet (b:bs) = foldr xor b bs

type Assignment = [(Int,Bool)]

anySat :: Bdd -> Maybe Assignment
anySat b
  | b == bot = Nothing
  | b == top = Just []
  | otherwise = Just ((n,hastobetrue):rest) where
      hastobetrue = elseOf b == bot
      (Just n)    = firstVarOf b
      (Just rest) = if hastobetrue then anySat (thenOf b) else anySat (elseOf b)

firstVarOf :: Bdd -> Maybe Int
firstVarOf b
  | b == bot = Nothing
  | b == top = Nothing
  | otherwise = Just (read $ Data.Boolean.CUDD.unbvar $ Data.Boolean.CUDD.bif b)

maxVarOf ::  Bdd -> Maybe Int
maxVarOf b
  | b == bot = Nothing
  | b == top = Nothing
  | otherwise = maximum [ Just v, m1, m2 ] where
      v = read $ Data.Boolean.CUDD.unbvar b :: Int
      m1 = maxVarOf $ thenOf b
      m2 = maxVarOf $ elseOf b

elseOf :: Bdd -> Bdd
elseOf = Data.Boolean.CUDD.belse

thenOf :: Bdd -> Bdd
thenOf = Data.Boolean.CUDD.bthen

gfp :: (Bdd -> Bdd) -> Bdd
gfp = Data.Boolean.CUDD.fix top

restrict :: Bdd -> (Int,Bool) -> Bdd
restrict b (n,bit) = Data.Boolean.CUDD.reduce b res where
  res = if bit then var n else neg (var n)

restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet b bits = Data.Boolean.CUDD.reduce b res where
  res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits

restrictLaw :: Bdd -> Bdd -> Bdd
restrictLaw = Data.Boolean.CUDD.reduce

-- | Get all satisfying assignments. These will be partial, i.e. only
-- contain (a subset of) the variables that actually occur in the BDD.
allSats :: Bdd -> [Assignment]
allSats b
  | b == bot = []
  | b == top = [ [] ]
  | otherwise =
      [ (n,True):rest | rest <- allSats (thenOf b) ] ++ [ (n,False):rest | rest <- allSats (elseOf b) ]
      where (Just n) = firstVarOf b

-- | Given a set of all variables, complete an assignment.
completeAss :: [Int] -> Assignment -> [Assignment]
completeAss allvars ass =
  if null (addvars ass)
    then [ass]
    else concatMap (completeAss allvars) (extend ass (head (addvars ass)))
  where
    addvars s = allvars \\ sort (map fst s)
    extend s v = [ (v,False):s, (v,True):s ]

-- | Get all complete assignments, given a set of all variables.
-- In particular this will include variables not in the BDD.
allSatsWith :: [Int] -> Bdd -> [Assignment]
allSatsWith allvars b = concatMap (completeAss allvars) (allSats b) where

-- | Given a set of all variables, get the number of satisfying assignments.
-- This should better be done without actually generating them.
satCountWith :: [Int] -> Bdd -> Int
satCountWith allvars b = length (allSatsWith allvars b)

ifthenelse :: Bdd -> Bdd -> Bdd -> Bdd
ifthenelse = Data.Boolean.CUDD.ifthenelse

-- | A simple tree definition.
data BddTree = Bot | Top | Var Int BddTree BddTree deriving (Show,Eq)

-- | Convert a BDD to a tree.
unravel :: Bdd -> BddTree
unravel b
  | b == bot = Bot
  | b == top = Top
  | otherwise = Var n (unravel (thenOf b)) (unravel (elseOf b)) where (Just n) = firstVarOf b

type Note = [Int]
data AnnotatedBdd = ATop Note | ABot Note | AVar Int AnnotatedBdd AnnotatedBdd Note deriving (Show,Eq)

varsOf :: BddTree -> [Int]
varsOf Top = []
varsOf Bot = []
varsOf (Var n lhs rhs) = sort $ nub (n: varsOf lhs ++ varsOf rhs)

noteOf :: AnnotatedBdd -> Note
noteOf (ABot n) = n
noteOf (ATop n) = n
noteOf (AVar _ _ _ n) = n

annotate :: BddTree -> AnnotatedBdd
annotate Bot = ABot [0]
annotate Top = ATop [1]
annotate (Var k lhs rhs) = AVar k (annotate lhs) (annotate rhs) $
  if noteOf (annotate lhs) == noteOf (annotate rhs)
    then noteOf (annotate lhs)
    else (k:noteOf (annotate lhs)) ++ (k:noteOf (annotate rhs))

allLabels :: AnnotatedBdd -> [Note]
allLabels ab = nub $ allLabels' ab where
  allLabels' (ABot n) = [n]
  allLabels' (ATop n) = [n]
  allLabels' (AVar _ lhs rhs l) = [l] ++ allLabels lhs ++ allLabels rhs

-- | Generate a string which describes the BDD in the dor language.
genGraph :: Bdd -> String
genGraph myb = genGraph' (unravel myb) where
  genGraph' (Bot) = "digraph g { Bot [label=\"0\",shape=\"box\"]; }"
  genGraph' (Top) = "digraph g { Top [label=\"1\",shape=\"box\"]; }"
  genGraph' b = "strict digraph g {\n" ++ genGraphStep (annotate b) ++ sinks ++ rankings ++ "}"
    where
      genGraphStep (AVar v lhs rhs l) =
        "n" ++ lp l ++ " [label=\"" ++ show v ++ "\",shape=\"circle\"];\n"
        ++ case lhs of
          (ATop _) -> "n"++ lp l ++" -> Top;\n"
          (ABot _) -> "n"++ lp l ++" -> Bot;\n"
          (AVar _ _ _ l') -> "n"++ lp l ++" -> n"++ lp l' ++";\n" ++ genGraphStep lhs
        ++ case rhs of
          (ATop _) -> "n"++ lp l ++" -> Top [style=dashed];\n"
          (ABot _) -> "n"++ lp l ++" -> Bot [style=dashed];\n"
          (AVar _ _ _ l') -> "n"++ lp l ++" -> n"++ lp l' ++" [style=dashed];\n" ++ genGraphStep rhs
      genGraphStep _ = ""
      sinks = "Bot [label=\"0\",shape=\"box\"];\n" ++ "Top [label=\"1\",shape=\"box\"];\n"
      rankings = concat [ "{ rank=same; "++ unwords (nub $ nodesOf v (annotate b)) ++ " }\n" | v <- varsOf b ]
      nodesOf _ (ABot _) = []
      nodesOf _ (ATop _) = []
      nodesOf v (AVar v' lhs rhs l) = if v==v' then ["n"++lp l] else nodesOf v lhs ++ nodesOf v rhs
      lp l = show n where (Just n) = lookup l nodelabelling
      nodelabelling = zip (allLabels (annotate b)) [(0::Int)..]

-- | Display the graph of a BDD with dot.
showGraph :: Bdd -> IO ()
showGraph b = do
  (inp,_,_,pid) <- runInteractiveProcess "/usr/bin/dot" ["-Tx11"] Nothing Nothing
  hPutStr inp (genGraph b)
  hFlush inp
  hClose inp
  _ <- waitForProcess pid
  return ()

-- | Relabel variables according to the given mapping.
relabel :: [(Int,Int)] -> Bdd -> Bdd
relabel [] b = b
relabel rel@((n,newn):rest) b
  | b == bot = b
  | b == top = b
  | otherwise = case compare n (fromJust (firstVarOf b)) of
                  LT -> relabel rest b
                  EQ -> ifthenelse (var newn) (relabel rest (thenOf b)) (relabel rest (elseOf b))
                  GT -> ifthenelse (var (fromJust (firstVarOf b))) (relabel rel (thenOf b)) (relabel rel (elseOf b))
