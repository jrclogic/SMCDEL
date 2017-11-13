module SMCDEL.Internal.MyHaskCUDD (
  -- * Types
  Bdd,
  -- * Creation of new BDDs
  top, bot, var,
  -- * Combination and Manipulation of BDDs
  neg, con, dis, imp, equ, xor, conSet, disSet, xorSet,
  exists, forall, forallSet, existsSet,
  restrict, restrictSet,
  ifthenelse,
  gfp
) where

import qualified Cudd.Cudd

type Bdd = Cudd.Cudd.DdNode

manager :: Cudd.Cudd.DdManager
manager = Cudd.Cudd.cuddInit

top :: Bdd
top = Cudd.Cudd.cuddReadOne manager

bot :: Bdd
bot = Cudd.Cudd.cuddReadLogicZero manager

var :: Int -> Bdd
var = Cudd.Cudd.cuddBddIthVar manager

neg :: Bdd -> Bdd
neg = Cudd.Cudd.cuddNot manager

xor :: Bdd -> Bdd -> Bdd
xor = Cudd.Cudd.cuddBddXor manager

exists :: Int -> Bdd -> Bdd
exists n b = Cudd.Cudd.cuddBddExistAbstract manager b (Cudd.Cudd.cuddIndicesToCube manager [n])

forall :: Int -> Bdd -> Bdd
forall n b = Cudd.Cudd.cuddBddUnivAbstract manager b (Cudd.Cudd.cuddIndicesToCube manager [n])

existsSet :: [Int] -> Bdd -> Bdd
existsSet [] b = b
existsSet ns b = Cudd.Cudd.cuddBddExistAbstract manager b (Cudd.Cudd.cuddIndicesToCube manager ns)

forallSet :: [Int] -> Bdd -> Bdd
forallSet [] b = b
forallSet ns b = Cudd.Cudd.cuddBddUnivAbstract manager b (Cudd.Cudd.cuddIndicesToCube manager ns)

equ :: Bdd -> Bdd -> Bdd
equ a b = con (imp a b) (imp b a)

imp :: Bdd -> Bdd -> Bdd
imp b1 b2 = Cudd.Cudd.cuddBddIte manager b1 b2 top

ifthenelse :: Bdd -> Bdd -> Bdd -> Bdd
ifthenelse = Cudd.Cudd.cuddBddIte manager

con :: Bdd -> Bdd -> Bdd
con = Cudd.Cudd.cuddBddAnd manager

dis :: Bdd -> Bdd -> Bdd
dis = Cudd.Cudd.cuddBddOr manager

conSet :: [Bdd] -> Bdd
conSet [] = top
conSet (b:bs) = foldl con b bs

disSet :: [Bdd] -> Bdd
disSet [] = bot
disSet (b:bs) = foldl dis b bs

xorSet :: [Bdd] -> Bdd
xorSet [] = bot
xorSet (b:bs) = foldl xor b bs

gfp :: (Bdd -> Bdd) -> Bdd
gfp operator = gfpLoop top where
  gfpLoop :: Bdd -> Bdd
  gfpLoop current =
    if current == operator current
      then current
      else gfpLoop (operator current)

restrict :: Bdd -> (Int,Bool) -> Bdd
restrict b (n,bit) = Cudd.Cudd.cuddBddLICompaction manager b res where
  res = if bit then var n else neg (var n)

restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet b bits = Cudd.Cudd.cuddBddLICompaction manager b res where
  res = conSet $ map (\(n,bit) -> if bit then var n else neg (var n)) bits
