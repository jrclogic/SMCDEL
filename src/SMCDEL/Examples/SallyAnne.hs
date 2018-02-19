module SMCDEL.Examples.SallyAnne where

import Data.Map.Strict (fromList)

import SMCDEL.Language
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.K.Change
import SMCDEL.Symbolic.S5 (boolBddOf)

pp, qq, tt :: Prp
pp = P 0
tt = P 1
qq = P 7 -- this number should not matter!

sallyInit :: BelScene
sallyInit = (BlS [pp, tt] law obs, actual) where
  law    = boolBddOf $ Conj [PrpF pp, Neg (PrpF tt)]
  obs    = fromList [ ("Sally", totalRelBdd), ("Anne", totalRelBdd) ]
  actual = [pp]

sallyPutsMarbleInBasket :: Event
sallyPutsMarbleInBasket = (Trf [] Top [tt]
  (fromList [ (tt,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate1 :: BelScene
sallyIntermediate1 = sallyInit `transform` sallyPutsMarbleInBasket

sallyLeaves :: Event
sallyLeaves = (Trf [] Top [pp]
  (fromList [ (pp,boolBddOf Bot) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate2 :: BelScene
sallyIntermediate2 = sallyIntermediate1 `transform` sallyLeaves

annePutsMarbleInBox :: Event
annePutsMarbleInBox = (Trf [qq] Top [tt]
  (fromList [ (tt,boolBddOf $ Conj [Neg (PrpF qq) `Impl` PrpF tt, PrpF qq `Impl` Bot]) ])
  (fromList [ ("Anne", allsamebdd [qq]), ("Sally", cpBdd $ boolBddOf $ Neg (PrpF qq))  ]), [qq])

sallyIntermediate3 :: BelScene
sallyIntermediate3 = sallyIntermediate2 `transform` annePutsMarbleInBox

sallyComesBack :: Event
sallyComesBack = (Trf [] Top [pp]
  (fromList [ (pp,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate4 :: BelScene
sallyIntermediate4 = sallyIntermediate3 `transform` sallyComesBack

sallyFinal :: BelScene
sallyFinal = sallyInit
              `transform` sallyPutsMarbleInBasket
              `transform` sallyLeaves
              `transform` annePutsMarbleInBox
              `transform` sallyComesBack

sallyFinalCheck :: (Bool,Bool)
sallyFinalCheck =
  ( SMCDEL.Symbolic.K.evalViaBdd sallyFinal (K "Sally" (PrpF tt))
  , sallyIntermediate4 == sallyFinal )
