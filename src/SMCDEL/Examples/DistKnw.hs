{-# LANGUAGE FlexibleInstances #-}
module SMCDEL.Examples.DistKnw where

import SMCDEL.Explicit.S5
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5

-- bob knows P 0 and alice knows that bob knows
distModelA :: PointedModelS5
distModelA = (KrMS5 [0,1] [(alice,[[0,1]]),(bob,[[0],[1]])] [ (0,[(P 0,True)]), (1,[(P 0,False)]) ], 0)

-- bob knows P 0 and alice does not know that bob knows
distModelB :: PointedModelS5
distModelB = (KrMS5 [0, 1, 2] [(alice,[[0,1,2]]),(bob,[[0],[1,2]])] [ (0,[(P 0,True)]), (1,[(P 0,True)]), (2,[(P 0,False)]) ], 0)

-- alice knows P 1, bob knows P 2: P 1 and P 2 are distributed knowledge
distMuddy :: PointedModelS5
distMuddy =
    (KrMS5 [0, 1, 2, 3] [ ( alice, [[0, 1], [2, 3]] ), ( bob, [[0, 2], [1, 3]] ) ]
    [(0, [(P 1,False), (P 2,False)]), (1, [(P 1,True), (P 2, False)]),
     (2, [(P 1,False), (P 2, True)]), (3, [(P 1,True), (P 2,True)])]
    , 3)

distKnForm :: Form
distKnForm = Dk [alice, bob] (Conj [PrpF (P 1), PrpF (P 2)])

resMuddy :: [Bool]
resMuddy =
    map (SMCDEL.Explicit.S5.eval distMuddy)
    [K alice (PrpF (P 1)), K bob (PrpF (P 2)), distKnForm]

muddyKNS :: KnowScene
muddyKNS = kripkeToKns distMuddy

resMuddyKNS :: [Bool]
resMuddyKNS =
    map (SMCDEL.Symbolic.S5.eval muddyKNS)
    [K alice (PrpF (P 1)), K bob (PrpF (P 2)), distKnForm]
