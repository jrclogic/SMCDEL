{-# LANGUAGE TemplateHaskell #-}

{- |

We model the The Sally-Anne false belief task, originally from [BLF1985] and
formalised in DEL in [B2014]. The story goes as follows:

> Sally has a basket, Anne has a box.
> Sally also has a marble and puts it in her basket.
> Then Sally goes out for a walk.
> Anne moves the marble from the basket into the Box.
> Now Sally comes back and wants to get her marble.
> Where will she look for it?

Adapted from

References:

- [BLF1985]
  Simon Baron-Cohen, Alan M. Leslie, Uta Frith (1985):
  /Does the autistic child have a “theory of mind”?/
  Cognition, volume 21, number 1, pages 37–46.
  <https://doi.org/10.1016/0010-0277(85)90022-8>

- [B2014]
  Thomas Bolander (2014):
  /Seeing is believing: Formalising false-belief tasks in dynamic epistemic logic/.
  ECSI-2014, pages 246–263.
  <https://ceur-ws.org/Vol-1283/paper_14.pdf>

- Malvin Gattinger (2017):
  /Towards Symbolic Factual Change in DEL/.
  ESSLLI 2017 Student Session, pages 14-24.
  <https://arxiv.org/abs/1912.10717>
  (Section 6)

-}

module SMCDEL.Examples.SallyAnne where

import Data.Map.Strict (fromList)

import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (boolBddOf)

-- * Vocabulary

{- $
The vocabulary is \(V = \{p, p_1\}\) where
  \(p\) (`P 0`) means that Sally is in the room and
  \(p_`\) (`P 1`) that the marble is in the basket.
-}

pp, qq, tt :: Prp
pp = P 0
tt = P 1
qq = P 7 -- this number does not matter


-- * Initial Structure

sallyInit :: BelScene
sallyInit = (BlS [pp, tt] law obs, actual) where
  law    = boolBddOf $ Conj [PrpF pp, Neg (PrpF tt)]
  obs    = fromList [ ("Sally", totalRelBdd), ("Anne", totalRelBdd) ]
  actual = [pp]
$(addSvg 'sallyInit)

-- * Sequence of actions

sallyPutsMarbleInBasket :: Event
sallyPutsMarbleInBasket = (Trf [] Top
  (fromList [ (tt,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])
$(addSvg 'sallyPutsMarbleInBasket)

sallyIntermediate1 :: BelScene
sallyIntermediate1 = sallyInit `update` sallyPutsMarbleInBasket
$(addSvg 'sallyIntermediate1)

sallyLeaves :: Event
sallyLeaves = (Trf [] Top
  (fromList [ (pp,boolBddOf Bot) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])
$(addSvg 'sallyLeaves)

sallyIntermediate2 :: BelScene
sallyIntermediate2 = sallyIntermediate1 `update` sallyLeaves
$(addSvg 'sallyIntermediate2)

-- | Anne puts the marble in the box, not observed by Sally.
-- We use `P 5` to distinguish the two possible events here.
annePutsMarbleInBox :: Event
annePutsMarbleInBox = (Trf [P 5] Top
  (fromList [ (tt,boolBddOf $ Conj [Neg (PrpF $ P 5) `Impl` PrpF tt, PrpF (P 5) `Impl` Bot]) ])
  (fromList [ ("Anne", allsamebdd [P 5]), ("Sally", cpBdd $ boolBddOf $ Neg (PrpF $ P 5))  ]), [P 5])
$(addSvg 'annePutsMarbleInBox)

sallyIntermediate3 :: BelScene
sallyIntermediate3 = sallyIntermediate2 `update` annePutsMarbleInBox
$(addSvg 'sallyIntermediate3)

sallyComesBack :: Event
sallyComesBack = (Trf [] Top
  (fromList [ (pp,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])
$(addSvg 'sallyComesBack)

-- * End of the story

-- | The result after all four updates.
--
-- >>> sallyFinal == sallyInit `updates` [ sallyPutsMarbleInBasket , sallyLeaves , annePutsMarbleInBox, sallyComesBack ]
-- True
--
sallyFinal :: BelScene
sallyFinal = sallyIntermediate3 `update` sallyComesBack
$(addSvg 'sallyFinal)

{- $
We check that in `sallyFinal` indeed Sally believes that the marble is in the basket (`tt`).

>>> sallyFinal |= K "Sally" (PrpF tt)
True
-}

-- TODO more detailed modelling:
-- change `annePutsMarbleInBox` to be unobserved by Sally iff she is away?
