module SMCDEL.Examples.LetterPassing where

import Data.List (sort)

import SMCDEL.Language
import SMCDEL.Symbolic.S5 hiding (announce)
import SMCDEL.Translations.S5 (booloutof)
import SMCDEL.Other.Planning

explain :: Prp -> String
explain (P k) | odd k     = "at " ++ show ((k + 1) `div` 2)
              | otherwise = "for " ++ show (k `div` 2)

atP, forP :: Int -> Prp
atP  k = P $ k*2 - 1
forP k = P $ k*2

at, for :: Int -> Form
at  = PrpF . atP
for = PrpF . forP

letterStart :: MultipointedKnowScene
letterStart = (KnS voc law obs, cur) where
  voc = sort $ map atP [1..3] ++ map forP [1..3]
  law = boolBddOf $ Conj $
    -- letter must be at someone, but not two:
       [ Disj (map at [1..3]) ]
    ++ [ Neg $ Conj [at i, at j] | i <- [1..3], j <- [1..3], i /= j ]
    -- letter must be for someone, but not two:
    ++ [ Disj (map for [1..3]) ]
    ++ [ Neg $ Conj [for i, for j] | i <- [1..3], j <- [1..3], i /= j ]
    -- make it common knowledge that the letter is at 1, but not adressed to 1:
    ++ [ at 1, Neg (for 1) ]
  obs = [ ("1",[atP 1, forP 1, forP 2, forP 3])
        , ("2",[atP 2])
        , ("3",[atP 3]) ]
  cur = booloutof [atP 1, forP 3] voc

letterPass :: Int -> Int -> Int -> Labelled MultipointedEvent
letterPass n i j = (label, (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top)) where
  offset      = n*2 -- ensure addprops does not overlap with vocabOf (letterStartFor n)
  label       = show i ++ "->" ++ show j
  addprops    = map P [(offset + 1)..(offset + n)]
  addlaw      = Conj $ at i : [ PrpF (P (offset + k)) `Equi` for k | k <- [1..n] ]
  -- publicly pass the letter from i to j:
  changeLaw   = [ (atP i, boolBddOf Bot), (atP j, boolBddOf Top) ]
  -- privately tell j who the receiver is:
  addObs      = [ (show k, if k == j then addprops else []) | k <- [1..n] ]

letterGoal :: Form
letterGoal = Conj [ for i `Impl` at i | i <- [1,2,3] ]

letter :: CoopTask MultipointedKnowScene MultipointedEvent
letter = CoopTask letterStart actions letterGoal where
  actions = [ (show i, letterPass 3 i j) | (i,j) <- [(1,2),(2,1),(2,3),(3,2)] ]

letterStartFor :: Int -> MultipointedKnowScene
letterStartFor n = (KnS voc law obs, cur) where
  voc = sort $ map atP [1..n] ++ map forP [1..n]
  law = boolBddOf $ Conj $
    -- letter must be at someone, but not two:
       [ Disj (map at [1..n]) ]
    ++ [ Neg $ Conj [at i, at j] | i <-[1..n], j <- [1..n], i /= j ]
    -- letter must be for someone, but not two:
    ++ [ Disj (map for [1..n]) ]
    ++ [ Neg $ Conj [for i, for j] | i <-[1..n], j <- [1..n], i /= j ]
    -- make it common knowledge that letter is at 1, but not adressed to 1:
    ++ [ at 1, Neg (for 1) ]
  obs = ("1", atP 1 : map forP [1..n]) : [ (show k, [atP k]) | k <- [2..n] ]
  cur = booloutof [atP 1, forP n] voc

letterLine :: Int -> CoopTask MultipointedKnowScene MultipointedEvent
letterLine n = CoopTask (letterStartFor n) actions goal where
  actions = [ (show i, letterPass n i j) | i <- [1..n], j <- [1..n], abs(i-j) == 1 ]
  goal = Conj [ for i `Impl` at i | i <- [1..n] ]
