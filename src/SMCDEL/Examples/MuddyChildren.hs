module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Map.Strict (fromList)

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.K

mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]

myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3

knows :: Int -> Form
knows i = Kw (show i) (PrpF $ P i)

nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

father :: Int -> Form
father n = Disj (map PrpF [P 1 .. P n])
mudScn0 :: KnowScene
mudScn0 = pubAnnounceOnScn myMudScnInit (father 3)

mudScn1 :: KnowScene
mudScn1 = pubAnnounceOnScn mudScn0 (nobodyknows 3)

mudScn2 :: KnowScene
mudKns2 :: KnowStruct
mudScn2@(mudKns2,_) = pubAnnounceOnScn mudScn1 (nobodyknows 3)

empty :: Int -> KnowScene
empty n = (KnS [] (boolBddOf Top) obs,[]) where
  obs    = [ (show i, []) | i <- [1..n] ]

buildMC :: Int -> Int -> Event
buildMC n m = (KnT vocab Top obs, map P [1..m]) where
  obs = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  vocab = map P [1..n]

mudBelScnInit :: Int -> Int -> SMCDEL.Symbolic.K.BelScene
mudBelScnInit n m = (SMCDEL.Symbolic.K.BlS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = fromList [(show i, SMCDEL.Symbolic.K.allsamebdd $ delete (P i) vocab) | i <- [1..n]]
  actual = [P 1 .. P m]

myMudBelScnInit :: SMCDEL.Symbolic.K.BelScene
myMudBelScnInit = mudBelScnInit 3 3
