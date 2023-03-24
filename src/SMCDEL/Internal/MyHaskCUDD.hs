{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SMCDEL.Internal.MyHaskCUDD (
  -- * Types
  Dd, B, Z, O1, O0, I1, I0, Manager,
  -- * conversion functions
  toB, toZ, toO1, toO0, toI1, toI0,
  Convert, convertToZDD,
  -- * Building and manipulating Dds
  top, bot, var, --base elements
  neg, swapChildNodes, --outer/output and inner/input negation
  con, dis, restrict, gfp,
  imp, equ, xor, ifthenelse,
  exists, forall, forallSet, existsSet,
  conSet, disSet, xorSet, restrictSet,
  restrictLaw, ddSwapVars, relabelFun, relabelWith, substitSimul,
  -- * BDDs only
  allSats, anySat, allSatsWith,
  -- * ZDD only
  sub0, sub1,
  makeManagerZ, swap,
  -- * other supporting functions
  makeManager, ite,
  sparsity, getSupport, getDependentVars, size,
  writeToDot, printDdInfo, returnDot,
  -- * function classes
  DdO, DdT, DdI, DdTOI, DdTO, DdCtx
  ) where

import qualified Cudd.Cudd
import System.IO.Temp (withSystemTempDirectory)
import Control.Arrow ((***))
import Data.List
import Data.Maybe (fromJust)
import Data.Bifunctor (bimap)

-- | A Binary Decision diagram with any of the five node eliminations.
newtype Dd x y z = ToDd Cudd.Cudd.DdNode deriving stock (Eq,Show)

-- | The first field indicates whether don't care nodes (B, traditional BDD rule) are removed
-- or those where "Then" leads to the 0 leaf node (Z, traditional ZDD rule).
data B
data Z
-- | The second field represents whether the 1 set (O1) of a given boolean function is represented or its complement, the 0 set (O0).
-- Because the traditional BDD rule is symetric, complementing it does not change the size of the structure.
-- Because the traditional ZDD rule is asymmetric towards the leaf nodes (and the edge types), complementing it can change the structure drastically.
-- Applying (output) negation on a traditional ZDD structure corresponds to changing the elimination rule from Then 0 to Then 1.
-- When representing a model (not) complementing the stored information is similar to either storing all possible states or all impossible states.
data O1
data O0
-- | The third field represents whether each variable is interpreted as its complement (I0) or not (I1).
-- Conversion between I1 and I0 is done by swapping the children of all nodes.
-- This changes the result of any Input assignment to the result of the complement Input assignment, and vice versa.
-- Because the traditional BDD rule is symetric, flipping its child edges does not change the size of the structure.
-- Because the traditional ZDD rule is asymmetric towards the edge types (and the leaf nodes), complementing it can change the structure drastically.
-- Applying input negation on a traditional ZDD structure corresponds to changing the elimination Then 0 to Else 0.
-- Applying both output and input negation results in the dual of the original stored boolean function.
data I1
data I0

-- | Collection of all contraints, in order to easily apply them when needed.
type DdCtx a b c = (DdTOI a b c, DdTO a b, DdT a, DdO a b, DdI a b c)

type Manager = Cudd.Cudd.DdManager

-- | Manager construction. When using ZDDs, CUDD requires initialisation of the variables beforehand.
makeManagerZ :: Int -> IO Cudd.Cudd.DdManager
makeManagerZ vocabCap = Cudd.Cudd.cuddInitZ (vocabCap +1)

-- | Manager construction when only using BDDs.
makeManager :: IO Cudd.Cudd.DdManager
makeManager = Cudd.Cudd.cuddInit


-- | functions that require the dd to be completely specified
class DdTOI a b c  where
    bot :: Cudd.Cudd.DdManager -> Dd a b c
    top :: Cudd.Cudd.DdManager -> Dd a b c
    var :: Cudd.Cudd.DdManager -> Int -> Dd a b c
    restrict :: Cudd.Cudd.DdManager -> Dd a b c -> (Int, Bool) -> Dd a b c

instance DdTOI B O1 I1 where
  bot mgr = ToDd (Cudd.Cudd.cuddReadLogicZero mgr)
  top mgr = ToDd (Cudd.Cudd.cuddReadOne mgr)
  var mgr n = ToDd (Cudd.Cudd.cuddBddIthVar mgr n)
  restrict mgr bz@(ToDd zb) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction mgr zb res where
    ToDd res = if bit then var mgr n `asTypeOf` bz else neg mgr (var mgr n `asTypeOf` bz)

instance DdTOI B O1 I0 where
  bot mgr = ToDd (Cudd.Cudd.cuddReadLogicZero mgr)
  top mgr = ToDd (Cudd.Cudd.cuddReadOne mgr)
  var mgr n = neg mgr $ ToDd (Cudd.Cudd.cuddBddIthVar mgr n)
  restrict mgr bz@(ToDd zb) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction mgr zb res where
    ToDd res = if bit then var mgr n `asTypeOf` bz else neg mgr (var mgr n `asTypeOf` bz) --double negation to make the restrict S independent

instance DdTOI B O0 I1 where
  bot mgr = ToDd (Cudd.Cudd.cuddReadOne mgr)
  top mgr = ToDd (Cudd.Cudd.cuddReadLogicZero mgr)
  var mgr n = neg mgr $ ToDd (Cudd.Cudd.cuddBddIthVar mgr n)
  restrict mgr bz@(ToDd zb) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction mgr zb res where
    ToDd res = if bit then neg mgr (var mgr n `asTypeOf` bz) else var mgr n `asTypeOf` bz

instance DdTOI B O0 I0 where
  bot mgr = ToDd (Cudd.Cudd.cuddReadOne mgr)
  top mgr = ToDd (Cudd.Cudd.cuddReadLogicZero mgr)
  var mgr n = neg mgr $ ToDd (Cudd.Cudd.cuddBddIthVar mgr n)
  restrict mgr bz@(ToDd zb) (n,bit) = ToDd $ Cudd.Cudd.cuddBddLICompaction mgr zb res where
    ToDd res = if bit then neg mgr (var mgr n `asTypeOf` bz) else var mgr n `asTypeOf` bz

instance DdTOI Z O1 I1 where
  bot mgr = ToDd (Cudd.Cudd.cuddZddReadZero mgr)
  top mgr = ToDd (Cudd.Cudd.cuddZddReadOne mgr)
  var mgr n = ToDd (Cudd.Cudd.cuddZddIthVar mgr n)
  restrict mgr zdd (n,bit) = if bit then dis mgr (sub1 mgr zdd n)(swap mgr (sub1 mgr zdd n) n) else dis mgr (sub0 mgr zdd n)(swap mgr (sub0 mgr zdd n) n)

instance DdTOI Z O1 I0 where
  bot mgr = ToDd (Cudd.Cudd.cuddZddReadZero mgr)
  top mgr = ToDd (Cudd.Cudd.cuddZddReadOne mgr)
  var mgr n = neg mgr $ ToDd (Cudd.Cudd.cuddZddIthVar mgr n)
  restrict mgr zdd (n,bit) = if bit then dis mgr (sub0 mgr zdd n)(swap mgr (sub0 mgr zdd n) n) else dis mgr (sub1 mgr zdd n)(swap mgr (sub1 mgr zdd n) n)

instance DdTOI Z O0 I1 where
  bot mgr = ToDd (Cudd.Cudd.cuddZddReadOne mgr)
  top mgr = ToDd (Cudd.Cudd.cuddZddReadZero mgr)
  var mgr n = neg mgr $ ToDd (Cudd.Cudd.cuddZddIthVar mgr n)
  restrict mgr zdd (n,bit) = if bit then con mgr (sub1 mgr zdd n)(swap mgr (sub1 mgr zdd n) n) else con mgr (sub0 mgr zdd n)(swap mgr (sub0 mgr zdd n) n)

instance DdTOI Z O0 I0 where
  bot mgr = ToDd (Cudd.Cudd.cuddZddReadOne mgr)
  top mgr = ToDd (Cudd.Cudd.cuddZddReadZero mgr)
  var mgr n = ToDd (Cudd.Cudd.cuddZddIthVar mgr n)
  restrict mgr zdd (n,bit) = if bit then con mgr (sub0 mgr zdd n)(swap mgr (sub0 mgr zdd n) n) else con mgr (sub1 mgr zdd n)(swap mgr (sub1 mgr zdd n) n)


-- | functions where B/Z needs to be specified
class DdT a where
    neg :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c
    ite :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c -> Dd a b c
    equ :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c
    swapChildNodes :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> [Int] -> Dd a b c
    gfp :: DdCtx a b c  => Cudd.Cudd.DdManager -> (Dd a b c -> Dd a b c) -> Dd a b c
    toZ :: (DdCtx a b c, DdTOI Z b c) => Cudd.Cudd.DdManager -> Dd a b c -> Dd Z b c
    toB :: (DdCtx a b c, DdTOI B b c) => Cudd.Cudd.DdManager -> Dd a b c -> Dd B b c
    ddSwapVars :: (DdCtx a b c) => Cudd.Cudd.DdManager -> Dd a b c -> [Int] -> [Int] -> Dd a b c -- assumes no overlapping in lists
    writeToDot :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c  -> String -> IO ()


instance DdT B where
  neg mgr (ToDd b) = ToDd $ Cudd.Cudd.cuddNot mgr b
  ite mgr (ToDd b1) (ToDd b2) (ToDd b3) = ToDd $ Cudd.Cudd.cuddBddIte mgr b1 b2 b3 -- context independent version of ifthenelse
  equ mgr a b = con mgr (imp mgr a b) (imp mgr b a)
  swapChildNodes mgr b [n] = con mgr (imp mgr (neg mgr (var mgr n)) (restrict mgr b (n,True) `asTypeOf` b)) (imp mgr (var mgr n) (restrict mgr b (n,False) `asTypeOf` b))
  swapChildNodes mgr b (n:ns) = con mgr (con mgr (imp mgr (neg mgr (var mgr n)) (restrict mgr b (n,True))) (con mgr (var mgr n) (restrict mgr b (n,False)))) (swapChildNodes mgr b ns)
  swapChildNodes _ b [] = b
  gfp mgr operator = gfpLoop (top mgr) where
    gfpLoop current =
      if current == operator current
        then current
        else gfpLoop (operator current)
  toZ mgr (ToDd b :: Dd a b c)
    | b == Cudd.Cudd.cuddReadLogicZero mgr = bot mgr :: Dd Z b c
    | otherwise = ToDd (Cudd.Cudd.cuddZddPortFromBdd mgr b)
  toB _ b = b
  ddSwapVars mgr (ToDd bdd) list1 list2 = ToDd $ Cudd.Cudd.cuddBddSwapVariables mgr bdd [Cudd.Cudd.cuddBddIthVar mgr x | x <- list1] [Cudd.Cudd.cuddBddIthVar mgr y | y <- list2]
  writeToDot mgr (ToDd zdd) = Cudd.Cudd.cuddBddToDot mgr zdd


instance DdT Z where
  neg mgr z = ite mgr z (ToDd (Cudd.Cudd.cuddZddReadZero mgr) `asTypeOf` z) (ToDd (Cudd.Cudd.cuddZddReadOne mgr) `asTypeOf` z)
  equ mgr a b = con mgr (imp mgr a b) (imp mgr b a)
  ite mgr (ToDd z1) (ToDd z2) (ToDd z3) = ToDd (Cudd.Cudd.cuddZddITE mgr z1 z2 z3) -- context independent version of ifthenelse
  swapChildNodes _  z  []      = z
  swapChildNodes mgr (ToDd z) [n] = ToDd $ Cudd.Cudd.cuddZddChange mgr z n
  swapChildNodes mgr (ToDd z) (n:ns) = swapChildNodes mgr (ToDd $ Cudd.Cudd.cuddZddChange mgr z n) ns
  gfp mgr operator = gfpLoop (top mgr) where
    gfpLoop current =
      if current == operator current
        then current
        else gfpLoop (operator current)
  toZ _ z = z
  toB mgr (ToDd b :: Dd a b c)
    | b == Cudd.Cudd.cuddReadLogicZero mgr = bot mgr :: Dd B b c
    | otherwise = ToDd (Cudd.Cudd.cuddZddPortToBdd mgr b)
  ddSwapVars mgr z [n1] [n2] = ifthenelse mgr (var mgr n2) (ifthenelse mgr (var mgr n1) a11 a10) (ifthenelse mgr (var mgr n1) a01 a00)
    where
      a11 = restrict mgr (restrict mgr z (n1, True)) (n2, True)
      a10 = restrict mgr (restrict mgr z (n1, True)) (n2, False)
      a01 = restrict mgr (restrict mgr z (n1, False)) (n2, True)
      a00 = restrict mgr (restrict mgr z (n1, False)) (n2, False)
  ddSwapVars mgr z (n1:ns1) (n2:ns2) = ddSwapVars mgr (ifthenelse mgr (var mgr n2) (ifthenelse mgr (var mgr n1) a11 a10) (ifthenelse mgr (var mgr n1) a01 a00)) ns1 ns2
    where
      a11 = restrict mgr (restrict mgr z (n1, True)) (n2, True)
      a10 = restrict mgr (restrict mgr z (n1, True)) (n2, False)
      a01 = restrict mgr (restrict mgr z (n1, False)) (n2, True)
      a00 = restrict mgr (restrict mgr z (n1, False)) (n2, False)
  ddSwapVars _ _ _ _ = error "lists for ZddSwapVar are not of equal length"
  writeToDot mgr (ToDd zdd) = Cudd.Cudd.cuddZddToDot mgr zdd


-- | functions where B/Z and O1/0 need to be specified
class DdTO a b where
  con :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c
  dis :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c
  xor :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c
  xor mgr z1 z2 = dis mgr a b where
    a = con mgr (neg mgr z1) z2
    b = con mgr z1 (neg mgr z2)
  exists :: DdCtx a b c => Cudd.Cudd.DdManager -> Int -> Dd a b c -> Dd a b c
  forall :: DdCtx a b c => Cudd.Cudd.DdManager -> Int -> Dd a b c -> Dd a b c
  existsSet :: DdCtx a b c => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> Dd a b c
  forallSet :: DdCtx a b c => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> Dd a b c

instance DdTO Z O1 where
  con mgr (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddIntersect mgr z1 z2)
  dis mgr (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddUnion mgr z1 z2)
  exists mgr n z = dis mgr (restrict mgr z (n, False)) (restrict mgr z (n, True))
  forall mgr n z = con mgr (restrict mgr z (n, False)) (restrict mgr z (n, True))
  existsSet _ [] z = z
  existsSet mgr [n] z = exists mgr n z
  existsSet mgr (n:ns) z = dis mgr (restrict mgr (existsSet mgr ns z) (n, False)) (restrict mgr (existsSet mgr ns z) (n, True))
  forallSet _ [] z = z
  forallSet mgr [n] z = forall mgr n z
  forallSet mgr (n:ns) z = con mgr (restrict mgr (forallSet mgr ns z) (n, False)) (restrict mgr (forallSet mgr ns z) (n, True))

instance DdTO Z O0 where
  con mgr (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddUnion mgr z1 z2)
  dis mgr (ToDd z1) (ToDd z2) = ToDd (Cudd.Cudd.cuddZddIntersect mgr z1 z2)
  exists mgr n z = dis mgr (restrict mgr z (n, False)) (restrict mgr z (n, True))
  forall mgr n z = con mgr (restrict mgr z (n, False)) (restrict mgr z (n, True))
  existsSet mgr [n] z = exists mgr n z
  existsSet mgr (n:ns) z = dis mgr (restrict mgr (existsSet mgr ns z) (n, False)) (restrict mgr (existsSet mgr ns z) (n, True))
  existsSet _ [] z = z
  forallSet mgr [n] z = forall mgr n z
  forallSet mgr (n:ns) z = con mgr (restrict mgr (forallSet mgr ns z) (n, False)) (restrict mgr (forallSet mgr ns z) (n, True))
  forallSet _ [] z = z

instance DdTO B O1 where
  con mgr (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddAnd mgr b1 b2
  dis mgr (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddOr mgr b1 b2
  xor mgr (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddXor mgr b1 b2
  exists mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr [n])
  forall mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr [n])
  existsSet mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr n)
  forallSet mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr n)

instance DdTO B O0 where
  con mgr (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddOr mgr b1 b2
  dis mgr (ToDd b1) (ToDd b2) = ToDd $ Cudd.Cudd.cuddBddAnd mgr b1 b2
  xor mgr (ToDd b1) (ToDd b2) = neg mgr $ ToDd $ Cudd.Cudd.cuddBddXor mgr b1 b2
  exists mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr [n])
  forall mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr [n])
  existsSet mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddUnivAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr n)
  forallSet mgr n (ToDd b) = ToDd $ Cudd.Cudd.cuddBddExistAbstract mgr b ( Cudd.Cudd.cuddIndicesToCube mgr n)

-- | functions where only O1/0 needs to specified
class DdO a b where
  toO0 :: (DdCtx a O0 c) => Cudd.Cudd.DdManager -> Dd a b c -> Dd a O0 c
  toO1 :: (DdCtx a O1 c) => Cudd.Cudd.DdManager -> Dd a b c -> Dd a O1 c
  ifthenelse :: DdCtx a b c  => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c -> Dd a b c

instance DdO a O1 where
  toO0 mgr (ToDd d :: Dd a b c) = neg mgr (ToDd d :: Dd a O0 c)
  toO1 _ d = d
  ifthenelse = ite -- context dependent version of ite

instance DdO a O0 where
  toO0 _ d = d
  toO1 mgr (ToDd d :: Dd a b c) = neg mgr (ToDd d :: Dd a O1 c)
  ifthenelse mgr d1 d2 d3 = ite mgr d1 d3 d2 -- context dependent version of ite

-- | functions where only I1/0 needs to specified
class DdI a b c where
  toI0 :: (DdCtx a b I0) => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> Dd a b I0
  toI1 :: (DdCtx a b I1) => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> Dd a b I1

instance DdI a b I1 where
  toI0 mgr domain (ToDd d :: Dd a b c) = swapChildNodes mgr (ToDd d :: Dd a b I0) (map fromEnum domain)
  toI1 _ _ d = d

instance DdI a b I0 where
  toI0 _ _ d = d
  toI1 mgr domain (ToDd d :: Dd a b c) = swapChildNodes mgr (ToDd d :: Dd a b I1) (map fromEnum domain)

-- | Convert a BDD to one of the four ZDD kinds.
class (Convert b c) where
  convertToZDD :: Cudd.Cudd.DdManager -> [Int] -> Dd B O1 I1 -> Dd Z b c

instance Convert O1 I1 where convertToZDD mgr _      =                              toZ mgr
instance Convert O1 I0 where convertToZDD mgr domain = toI0 mgr domain            . toZ mgr
instance Convert O0 I1 where convertToZDD mgr _      =                   toO0 mgr . toZ mgr
instance Convert O0 I0 where convertToZDD mgr domain = toI0 mgr domain . toO0 mgr . toZ mgr

-- | functions where no specification is needed.
-- todo add these under the general class, instead of them being standalone functions?

imp :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> Dd a b c -> Dd a b c
imp mgr b1 = dis mgr (neg mgr b1)
conSet :: DdCtx a b c => Cudd.Cudd.DdManager -> [Dd a b c] -> Dd a b c
conSet mgr [] = top mgr
conSet mgr (b:bs) = foldl' (con mgr) b bs
disSet :: DdCtx a b c => Cudd.Cudd.DdManager -> [Dd a b c] -> Dd a b c
disSet mgr [] = bot mgr
disSet mgr (b:bs) = foldl' (dis mgr) b bs
xorSet :: DdCtx a b c => Cudd.Cudd.DdManager -> [Dd a b c] -> Dd a b c
xorSet mgr [] = top mgr
xorSet mgr (b:bs) = foldl' (xor mgr) b bs
restrictSet :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> [(Int, Bool)] -> Dd a b c
restrictSet mgr = foldl' (restrict mgr)

-- | Restrict with a law. Note that the law is the second parameter!
restrictLaw :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> Dd a b c -> Dd a b c
restrictLaw mgr v d = loop (getDependentVars mgr v d) d where
  loop (n:ns) bdd law
    | law == top mgr = bdd -- the law completely covers the bdd thus all nodes are restricted out
    | (bdd == top mgr) || (bdd == bot mgr) = bdd -- the bdd is already top/bot, restricting it further does not change anything
    | law == bot mgr = top mgr
    -- otherwise do the recursive restriction until terminal cases are met
    | otherwise = (var mgr n `conj` loop ns (restr bdd (n, True)) (restr law (n, True) )) `disj` (neg mgr (var mgr n) `conj` loop ns (restr bdd (n, False)) (restr law (n, False))) where
      disj = dis mgr
      conj = con mgr
      restr = restrict mgr
  loop [] bdd law
    | law == top mgr = bdd -- the law completely covers the bdd thus all nodes are restricted out
    | (bdd == top mgr) || (bdd == bot mgr) = bdd -- the bdd is already top/bot, restricting it further does not change anything
    | law == bot mgr = top mgr
    | otherwise = error "impossible? something went wrong in restrictLaw."

-- todo add faster restrictlaw for bdds?
{-}
restrictLawBDD :: Cudd.Cudd.DdManager -> Dd B b c -> Dd B b c -> Dd B b c
restrictLawBDD mgr (ToDd b) (ToDd law) = ToDd $ Cudd.Cudd.cuddBddRestrict mgr b law
-}

-- | Relabel a DD with a function. Assumption: no int is mapped to itself by rF.
relabelFun :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Int] -> (Int -> Int) -> Dd a b c -> Dd a b c
relabelFun mgr v rF dd = loop dd disjointListOfLists
  where

  --get indexes of "overlapping" integers positions (integers in l2 that also occur in L1)
  --and use that to return the corresponding elements in a tuple
  getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexesOverlap l1 l2), l1 `intersect` l2)
  indexesOverlap l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
  indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

  -- swap the (overlapping l1 ints with the corresponding l1 ints)
  -- in the not overlapping l1 values we look for the overlapping l2 values

  newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

  -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
  -- by removing the "overlapping" variables and performing a recursive call with them
  splitCompare [] [] = []
  splitCompare [] _  = error "varlists used for relabeling do not have equal length."
  splitCompare _  [] = error "varlists used for relabeling do not have equal length."
  splitCompare l1 l2 = bimap (l1 \\) (l2 \\) (getOverlap l1 l2) : uncurry splitCompare (newOverlap l1 l2)

  -- apply the function above to the support variable integers and the resulting integers from applying rf (the Remapping Function)
  -- and turn the integers into DD nodes (as ddSwapVars requires this)
  disjointListOfLists = splitCompare support (map rF support)
  support = getDependentVars mgr v dd

  -- loop and uncurry ddSwapVars so that it can be applied to the disjointListOfNodeLists
  loop b (n:ns) = loop (uncurry (ddSwapVars mgr b) n) ns
  loop b [] = b

-- | Relabel a DD with a list of pairs.
relabelWith :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [(Int,Int)] -> Dd a b c -> Dd a b c
relabelWith mgr r dd = loop dd disjointListOfLists where
  --get indexes of "overlapping" integers positions (integers in l2 that also occur in L1)
  --and use that to return the corresponding elements in a tuple
  getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexes l1 l2), l1 `intersect` l2)
  indexes l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
  indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

  -- swap the (overlapping l1 ints with the corresponding l1 ints)
  -- in the non overlapping l1 values we look for the overlapping l2 values

  newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

  -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
  -- by removing the "overlapping" variables and performing a recursive call with them
  splitCompare [] [] = []
  splitCompare [] _  = error "varlists used for relabeling do not have equal length."
  splitCompare _  [] = error "varlists used for relabeling do not have equal length."
  splitCompare l1 l2 = bimap (l1 \\) (l2 \\) (getOverlap l1 l2) : uncurry splitCompare (newOverlap l1 l2)

  -- apply the function above to the support variable integers and the resulting integers from applying rf (the Remapping Function)
  -- and turn the integers into BDD nodes (as ddSwapVars requires this)
  disjointListOfLists = splitCompare listVars1 listVars2

  loop b (n:ns) = loop (uncurry (ddSwapVars mgr b) n) ns
  loop b [] = b

  listIntPairs = sort $ map (fromEnum *** fromEnum) $ filter (uncurry (/=)) r
  (listVars1,listVars2) = unzip listIntPairs

-- | Simultaneous substitution.
-- Implemented via `ifte` and `restrict`.
substitSimul :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [(Int, Dd a b c)] -> Dd a b c -> Dd a b c
substitSimul _ [] dd = dd
substitSimul mgr ((n, psi) : ns) dd = ifte psi ( recurs (restr dd (n, True))) (recurs (restr dd (n, False)))
  where
  recurs = substitSimul mgr ns
  ifte = ifthenelse mgr
  restr = restrict mgr

-- * supporting functions

returnDot :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> IO String
returnDot mgr d = withSystemTempDirectory "smcdel" $ \tmpdir -> do
    writeToDot mgr d (tmpdir ++ "/temp.dot")
    readFile (tmpdir ++ "/temp.dot")

printDdInfo :: Cudd.Cudd.DdManager -> Dd a b c  -> String -> IO ()
printDdInfo mgr (ToDd zdd) str = do
  putStrLn str
  Cudd.Cudd.cuddPrintDdInfo mgr zdd
  return ()

size :: Cudd.Cudd.DdManager -> Dd a b c -> Int
size mgr (ToDd dd)
  | dd == Cudd.Cudd.cuddZddReadZero mgr = 0
  | otherwise = Cudd.Cudd.cuddDagSize dd

-- | Given a DD and the maximum variable, calculate the sparsity of the encoded set of state.
sparsity :: Cudd.Cudd.DdManager -> Dd a b c -> Int -> Double
sparsity mgr (ToDd b) n = Cudd.Cudd.cuddCountMinterm mgr b n / (2 ** fromIntegral n)

getSupport :: Cudd.Cudd.DdManager -> Dd a b c -> [Int]
getSupport mgr (ToDd dd) = [ n | (n,True) <- zip [0..] $ Cudd.Cudd.cuddSupportIndex mgr dd ]

-- | Given the full vocabulary and a DD, return the list of variables that the DD depends on.
-- Note that for ZDDs the support is not the same as the set of dependent variables.
getDependentVars :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Int] -> Dd a b c -> [Int]
getDependentVars mgr v dd = filter (\n -> restrict mgr dd (n, True) /= restrict mgr dd (n, False)) v

-- * ZDD only functions

-- restricts, but thus also removes variable from domain
sub0 :: Cudd.Cudd.DdManager -> Dd Z a b -> Int -> Dd Z a b
sub0 mgr (ToDd z) n = ToDd $ Cudd.Cudd.cuddZddSub0 mgr z n

sub1 :: Cudd.Cudd.DdManager -> Dd Z a b -> Int -> Dd Z a b
sub1 mgr (ToDd z) n = ToDd $ Cudd.Cudd.cuddZddSub1 mgr z n

swap :: (DdCtx Z b c) => Cudd.Cudd.DdManager -> Dd Z b c -> Int -> Dd Z b c
swap mgr (ToDd z) n = ToDd $ Cudd.Cudd.cuddZddChange mgr z n

-- * BDD only functions

-- | An assignment of boolean values to variables/integers.
type Assignment = [(Int,Bool)]

bitsToAss :: [Cudd.Cudd.SatBit] -> [Assignment]
bitsToAss = loop 0 where
  loop _ [] = [ [] ]
  loop n (Cudd.Cudd.DontCare:rest) = loop (n+1) rest
  loop n (Cudd.Cudd.Zero    :rest) = [ (n,False) : restA | restA <- loop (n+1) rest ]
  loop n (Cudd.Cudd.One     :rest) = [ (n,True ) : restA | restA <- loop (n+1) rest ]

-- | Get all satisfying assignments. These will be partial, i.e. only
-- contain (a subset of) the variables that actually occur in the BDD.
allSats :: Cudd.Cudd.DdManager -> Dd B O1 I1 -> [Assignment]
allSats mgr (ToDd b) = concatMap bitsToAss $ Cudd.Cudd.cuddAllSat mgr b

-- | Get the lexicographically smallest satisfying assignment, if there is any.
anySat :: Cudd.Cudd.DdManager -> Dd B O1 I1 -> Maybe Assignment
anySat mgr (ToDd b) = head . bitsToAss <$> Cudd.Cudd.cuddOneSat mgr b

-- | Given a set of all variables, complete an assignment.
completeAss :: [Int] -> Assignment -> [Assignment]
completeAss allvars ass =
  if null (addvars ass)
    then [ass]
    else concatMap (completeAss allvars) (extend ass (head (addvars ass)))
  where
    addvars s = allvars \\ sort (map fst s)
    extend s v = [ (v,False):s, (v,True):s ]

-- | Get all complete satisfying assignments, given a set of all variables.
-- In particular this will include variables not in the BDD.
allSatsWith :: Cudd.Cudd.DdManager -> [Int] -> Dd B O1 I1 -> [Assignment]
allSatsWith mgr allvars b = concatMap (completeAss allvars) (allSats mgr b)
