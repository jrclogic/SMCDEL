module MyHaskCUDD (
  -- * Types
  Bdd, Assignment,
  -- * Creation of new BDDs
  top, bot, var,
  -- * Combination and Manipulation of BDDs
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  exists, forall, forallSet, existsSet,
  restrict, restrictSet,
  ifthenelse, gfp, relabel,
  -- * Get satisfying assignments
  allSats, allSatsWith, satCountWith, anySat,
  -- * Show and convert to trees
  showGraph, genGraph, maxVarOf
) where

import Data.List
import System.Process
import System.IO
import qualified Cudd.Cudd

type Bdd = Cudd.Cudd.DDNode

manager :: Cudd.Cudd.DDNode
manager = Cudd.Cudd.cuddInit

top :: Bdd
top = Cudd.Cudd.readOne manager

bot :: Bdd
bot = Cudd.Cudd.readLogicZero manager

var :: Int -> Bdd
var = Cudd.Cudd.ithVar manager

neg :: Bdd -> Bdd
neg = Cudd.Cudd.bNot manager

xor :: Bdd -> Bdd -> Bdd
xor = Cudd.Cudd.bXor manager

exists :: Int -> Bdd -> Bdd
exists n = Cudd.Cudd.bExists manager (Cudd.Cudd.indicesToCube manager [n])

forall :: Int -> Bdd -> Bdd
forall n = Cudd.Cudd.bForall manager (Cudd.Cudd.indicesToCube manager [n])

existsSet :: [Int] -> Bdd -> Bdd
existsSet ns = Cudd.Cudd.bExists manager (Cudd.Cudd.indicesToCube manager ns)

forallSet :: [Int] -> Bdd -> Bdd
forallSet ns = Cudd.Cudd.bForall (Cudd.Cudd.indicesToCube manager ns)

equ :: Bdd -> Bdd -> Bdd
equ a b = con (imp a b) (imp b a) -- FIXME

imp :: Bdd -> Bdd -> Bdd
imp = Cudd.Cudd.lEq manager

con :: Bdd -> Bdd -> Bdd
con = Cudd.Cudd.bAnd manager

dis :: Bdd -> Bdd -> Bdd
dis = Cudd.Cudd.bOr manager

conSet :: [Bdd] -> Bdd
conSet [] = top
conSet (b:bs) =
  if bot `elem` (b:bs)
    then bot
    else foldl con b bs

disSet :: [Bdd] -> Bdd
disSet [] = bot
disSet (b:bs) =
  if top `elem` (b:bs)
    then top
    else foldl dis b bs

xorSet :: [Bdd] -> Bdd
xorSet [] = bot
xorSet (b:bs) = foldl xor b bs

-- type Assignment = [(Int,Bool)]
--
-- anySat :: Bdd -> Maybe Assignment
-- anySat b
--   | b == bot = Nothing
--   | b == top = Just []
--   | otherwise = Just ((n,hastobetrue):rest) where
--       hastobetrue = elseOf b == bot
--       (Just n)    = firstVarOf b
--       (Just rest) = if hastobetrue then anySat (thenOf b) else anySat (elseOf b)

-- firstVarOf :: Bdd -> Maybe Int
-- firstVarOf b
--   | b == bot = Nothing
--   | b == top = Nothing
--   | otherwise = Just (read $ Cudd.Cudd.unbvar $ Cudd.Cudd.bif b)
--   fst $ head $ filter snd (zip [0..] (Cudd.Cudd.supportIndex manager b))

-- maxVarOf ::  Bdd -> Maybe Int
-- maxVarOf b
--   | b == bot = Nothing
--   | b == top = Nothing
--   | otherwise = maximum [ Just $ v - (1::Int), m1, m2 ] where
--       v = ...
--       m1 = maxVarOf $ thenOf b
--       m2 = maxVarOf $ elseOf b

-- elseOf :: Bdd -> Bdd
-- elseOf = Cudd.Cudd.belse

-- thenOf :: Bdd -> Bdd
-- thenOf = Cudd.Cudd.bthen

-- gfp :: (Bdd -> Bdd) -> Bdd
-- gfp = Cudd.Cudd.fix top

-- restrict :: Bdd -> (Int,Bool) -> Bdd

-- restrict :: Bdd -> (Int,Bool) -> Bdd
-- restrict b (n,bit) = Cudd.Cudd.reduce b res where
--   res = if bit then var n else neg (var n)

-- restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
-- restrictSet b bits = Cudd.Cudd.reduce b res where
--   res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits
{-
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
ifthenelse = Cudd.Cudd.ifthenelse

-- | A simple tree definition.
data BddTree = Bot | Top | Var Int BddTree BddTree deriving (Show,Eq)

-- | Convert a BDD to a tree.
unravel :: Bdd -> BddTree
unravel b
  | b == bot = Bot
  | b == top = Top
  | otherwise = Var n (unravel (thenOf b)) (unravel (elseOf b)) where (Just n) = firstVarOf b

-- | Convert a tree to a BDD.
ravel :: BddTree -> Bdd
ravel Bot = bot
ravel Top = top
ravel (Var n nthen nelse) = ifthenelse (var n) (ravel nthen) (ravel nelse)

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

-- | Relabel variables according to the given mapping. Note that we
-- unravel the whole BDD, hence this is an expensive operation.
relabel :: [(Int,Int)] -> Bdd -> Bdd
relabel mapping b = ravel $ relabelTree mapping (unravel b)

-- relabel variables
relabelTree :: [(Int,Int)] -> BddTree -> BddTree
relabelTree _   Top = Top
relabelTree _   Bot = Bot
relabelTree rel (Var n left right) = Var newn (relabelTree rel left) (relabelTree rel right) where
  newn = case lookup n rel of
	      (Just m) -> m
	      Nothing  -> n-}
