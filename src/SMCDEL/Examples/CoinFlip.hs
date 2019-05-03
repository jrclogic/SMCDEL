module SMCDEL.Examples.CoinFlip where

import Data.Map.Strict (fromList)
import Data.List ((\\))

import SMCDEL.Language
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Symbolic.K

coinStart :: BelScene
coinStart = (BlS [P 0] law obs, actual) where
  law    = boolBddOf (PrpF $ P 0)
  obs    = fromList [ ("a", allsamebdd [P 0]), ("b", allsamebdd [P 0]) ]
  actual = [P 0]

flipRandomAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipRandomAndShowTo everyone p i = (Trf [q] eventlaw changelaw obs, [q]) where
  q = freshp [p]
  eventlaw = Top
  changelaw = fromList [ (p, boolBddOf $ PrpF q) ]
  obs = fromList $
    (i, allsamebdd  [q]) :
    [ (j,totalRelBdd) | j <- everyone \\ [i] ]

coinFlip :: Event
coinFlip = flipRandomAndShowTo ["a","b"] (P 0) "b"

coinResult :: BelScene
coinResult = coinStart `update` coinFlip
