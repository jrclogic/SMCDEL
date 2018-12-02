module SMCDEL.Internal.TaggedBDD where

import Data.Tagged
import Data.HasCacBDD hiding (Top,Bot)

import SMCDEL.Language

class TagForBDDs a where
  -- | How many copies of the vocabulary do we have?
  -- This is the number of markers + 1.
  multiplier :: Tagged a Bdd -> Int
  multiplier _ = 2
  -- | move back, must be without markers!
  unmvBdd :: Tagged a Bdd -> Bdd
  unmvBdd = relabelFun (\n -> if even n then n `div` 2 else error ("Odd: " ++ show n)) . untag
  -- | move into double vocabulary, but do not add marker
  mv :: Bdd -> Tagged a Bdd
  mv = cpMany 0
  -- | move into extended vocabulary, add one marker
  cp :: Bdd -> Tagged a Bdd
  cp = cpMany 1
  -- | move into extended vocabulary, add k many markers, MUST be available!
  cpMany :: Int -> Bdd -> Tagged a Bdd
  cpMany k b = let x = pure $ relabelFun (\n -> (2*n) + k) b
                in if k >= multiplier x then error "Not enough markers!" else x

  tagBddEval :: [Prp] -> Tagged a Bdd -> Bool
  tagBddEval truths querybdd = evaluateFun (untag querybdd) (\n -> P n `elem` truths)
  totalRelBdd, emptyRelBdd :: Tagged a Bdd
  totalRelBdd = pure top
  emptyRelBdd = pure bot

data Dubbel
instance TagForBDDs Dubbel where
  multiplier = const 2

data Tripel
instance TagForBDDs Tripel where
  multiplier = const 3

data Quadrupel
instance TagForBDDs Quadrupel where
  multiplier = const 4

allsamebdd :: TagForBDDs a => [Prp] -> Tagged a Bdd
allsamebdd ps = conSet <$> sequence [ equ <$> mv (var x) <*> cp (var x) | (P x) <- ps ]
