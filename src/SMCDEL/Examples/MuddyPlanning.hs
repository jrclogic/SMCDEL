module SMCDEL.Examples.MuddyPlanning where

import SMCDEL.Examples.MuddyChildren
import SMCDEL.Language
import SMCDEL.Other.Planning

toyPlan :: [OfflinePlan]
toyPlan = offlineSearch maxSteps start acts cons goal where
  maxSteps = 5 -- 2 would be enough
  start = mudScnInit 3 2
  acts = Disj [PrpF (P k) | k <- [1,2,3]] : [Neg $ Kw (show k) $ PrpF (P k) | k <- [1,2,3]]
  cons = [ Neg $ Kw "2" (PrpF $ P 2) ]
  goal = Kw "1" (PrpF $ P 1)
