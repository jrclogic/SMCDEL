{- |
We model the story of the muddy children which is known in many versions.
See for example~\cite{Littlewood1953:amm},~\cite[p.~24-30]{fagin1995reasoning} or~\cite[p.~93-96]{DitHoekKooi2007:del}.

Our implementation treats the general case for \(n\) children out of which \(m\) are muddy, but we focus on the case of three children who are all muddy.
As usual, all children can observe whether the others are muddy but do not see their own face.
This is represented by the observational variables:
Agent $1$ observes $p_2$ and $p_3$, agent $2$ observes $p_1$ and $p_3$ and agent $3$ observes $p_1$ and $p_2$.
-}

module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Maybe (fromJust)
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (seteq)
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.K
import qualified SMCDEL.Explicit.K

-- | The initial knowledge structure, given the total number of children, and the number of muddy children.
mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]

-- | The initial structure for 3 muddy children.
myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3

-- | A formula to say that the given child knows whether it is muddy.
knows :: Int -> Form
knows i = Kw (show i) (PrpF $ P i)

-- | A formula to say that none out of \(n\) children knows its own state.
nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

-- | Announcement of the father announce that someone is muddy.
father :: Int -> Form
father n = Disj (map PrpF [P 1 .. P n])

-- | Result after announcing `father 3` in `myMudScnInit`.
mudScn0 :: KnowScene
mudScn0 = update myMudScnInit (father 3)

mudScn1 :: KnowScene
mudScn1 = update mudScn0 (nobodyknows 3)

mudScn2 :: KnowScene
mudKns2 :: KnowStruct
mudScn2@(mudKns2,_) = update mudScn1 (nobodyknows 3)

empty :: Int -> KnowScene
empty n = (KnS [] (boolBddOf Top) obs,[]) where
  obs    = [ (show i, []) | i <- [1..n] ]

buildMC :: Int -> Int -> Event
buildMC n m = (noChange KnTrf vocab Top obs, map P [1..m]) where
  obs = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  vocab = map P [1..n]

buildResult :: KnowScene
buildResult = empty 3 `update` buildMC 3 3

mudGenKrpInit :: Int -> Int -> SMCDEL.Explicit.K.PointedModel
mudGenKrpInit n m = (SMCDEL.Explicit.K.KrM $ fromList wlist, cur) where
  wlist = [ (w, (fromList (vals !! w), fromList $ relFor w)) | w <- ws ]
  ws    = [0..(2^n-1)]
  vals  = map sort (foldl buildTable [[]] [P k | k<- [1..n]])
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor w = [ (show i, seesFrom i w) | i <- [1..n] ]
  seesFrom i w = filter (\v -> samefor i (vals !! w) (vals !! v)) ws
  samefor i ps qs = seteq (delete (P i) (map fst $ filter snd ps)) (delete (P i) (map fst $ filter snd qs))
  cur = fromJust (elemIndex curVal vals)
  curVal = sort $ [(p,True) | p <- [P 1 .. P m]] ++ [(p,True) | p <- [P (m+1) .. P n]]

myMudGenKrpInit :: SMCDEL.Explicit.K.PointedModel
myMudGenKrpInit = mudGenKrpInit 3 3

mudBelScnInit :: Int -> Int -> SMCDEL.Symbolic.K.BelScene
mudBelScnInit n m = (SMCDEL.Symbolic.K.BlS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = fromList [(show i, SMCDEL.Symbolic.K.allsamebdd $ delete (P i) vocab) | i <- [1..n]]
  actual = [P 1 .. P m]

myMudBelScnInit :: SMCDEL.Symbolic.K.BelScene
myMudBelScnInit = mudBelScnInit 3 3
