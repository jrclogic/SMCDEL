module SMCDEL.Examples.Prisoners where

import Data.HasCacBDD hiding (Top,Bot)
import Data.Map.Strict (fromList)

import SMCDEL.Explicit.K
import SMCDEL.Explicit.K.Change
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.K.Change
import SMCDEL.Symbolic.S5 (boolBddOf)

-- P 0 -- light is on
-- P i -- agent i has been in the room (and switched on the light)
-- agents: 1 is the counter, 2 and 3 are the others

prisonExpStart :: KripkeModel
prisonExpStart =
  KrM $ fromList [ (1, (fromList [(P 0,False),(P 1,False),(P 2,False),(P 3,False)], fromList [("1",[1])])) ]

prisonGoal :: Form
prisonGoal = Disj [ K i everyoneWasInTheRoom | i <- ["1"] ] where
  everyoneWasInTheRoom = Conj [ PrpF $ P k | k <- [1,2,3] ]

prisonAction :: ChangeModel
prisonAction = ChM $ fromList actions where
  p = PrpF (P 0)
  [p2,p3] = map (PrpF . P) [2,3]
  actions =
    [ (1, Ch p       (fromList [(P 0, Bot), (P 1, Top)                ]) (fromList [("1",[1    ])]))
    , (2, Ch (Neg p) (fromList [            (P 1, Top)                ]) (fromList [("1",[2    ])]))
    , (3, Ch Top     (fromList [(P 0, p2 `Impl` p), (P 2, p `Impl` p2)]) (fromList [("1",[3,4,5])])) -- interview 2
    , (4, Ch Top     (fromList [(P 0, p3 `Impl` p), (P 3, p `Impl` p3)]) (fromList [("1",[3,4,5])])) -- interview 3
    -- , (5, Ch Top  (fromList [ ]) (fromList [("1",[3,4,5])])) -- nothing happens, ignored for now
    ]

prisonInterview :: Integer -> MultipointedChangeModel
prisonInterview 1 = (prisonAction, [1,2])
prisonInterview 2 = (prisonAction, [3])
prisonInterview 3 = (prisonAction, [4])
prisonInterview _ = undefined

newtype KripkeStory = KrpStory (PointedModel,[MultipointedChangeModel])

endOfStory :: KripkeStory -> PointedModel
endOfStory (KrpStory (start,actions)) = foldl productChangeMulti start actions

instance TexAble KripkeStory where
  tex (KrpStory (start,actions)) = adjust (tex start) ++ loop start actions where
    adjust thing = "\\raisebox{-.5\\height}{\\begin{adjustbox}{max height=4cm, max width=7cm}" ++ thing ++ "\\end{adjustbox}}"
    loop _       [] = ""
    loop current (a:as) =
      let
        new = generatedSubmodel $ current `productChangeMulti` a
      in
        " \\times " ++ adjust (tex a) ++ " = " ++ adjust (tex new) ++ "\\] \\[ " ++ loop new as

prisonExp :: KripkeStory
prisonExp = KrpStory ((prisonExpStart,1), map prisonInterview [2,1,3,1])

prisonExpResult :: PointedModel
prisonExpResult = endOfStory prisonExp

prisonSymStart :: BelScene
prisonSymStart = (BlS (map P [0..3]) law obs, actual) where
  law    = boolBddOf (Conj [ Neg $ PrpF $ P k | k <- [0..3]])
  -- Light off, nobody has been in the room, this is common knowledge.
  obs    = fromList [ ("1", pure top), ("2", pure top), ("3", pure top) ]
  actual = []

prisonSymInterview :: Int -> MultiEvent
prisonSymInterview 1 = (prisonSymEvent, [undefined])
prisonSymInterview 2 = (prisonSymEvent, [undefined])
prisonSymInterview 3 = (prisonSymEvent, [undefined])
prisonSymInterview _ = undefined

prisonSymEvent :: Transformer
prisonSymEvent = Trf -- agent 1 is interviewd
  (map P [7,8,9]) -- distinguish six events using fresh variables:
  -- p7 iff the light was on
  -- p8 p9 - interview 1
  -- p8    - interview 2
  --    p9 - interview 3
  --       - forbid!
  (PrpF (P 7) `Equi` PrpF (P 0))  -- p7 hapens iff light is on aka p0
  [P 0, P 1, P 2, P 3] -- light might be turned off and visits of agents recorded
  (fromList [ (P 0, boolBddOf $ Conj [PrpF (P 7) `Impl` Bot, Neg (PrpF (P 7)) `Impl` PrpF (P 0)])
            , (P 1, top) ]) -- changelaw

  (fromList
    -- agent 1 observes whether (p8 && p9) and if true, observes p7
    [("1", allsamebdd [P 7])
    ,("2", pure top),("3", pure top)])

prisonSymEvent' :: Transformer
prisonSymEvent' = Trf -- agent 2 or 3 is interviewd
  [P 7] Top -- p7 iff interviewee is 2
  [P 0, P 2, P 3] -- light p0 might be turned on and visits of 2 and 3 recorded
  (fromList [ (P 0, boolBddOf $ Conj
                      [      PrpF (P 7)  `Impl` (PrpF (P 2) `Impl` PrpF (P 0))
                      , Neg (PrpF (P 7)) `Impl` (PrpF (P 3) `Impl` PrpF (P 0)) ] )
            , (P 2, boolBddOf $ Conj
                      [      PrpF (P 7)  `Impl` (PrpF (P 0) `Impl` PrpF (P 2))
                      , Neg (PrpF (P 7)) `Impl` PrpF (P 2) ] )
            , (P 3, boolBddOf $ Conj
                      [ Neg (PrpF (P 7)) `Impl` (PrpF (P 0) `Impl` PrpF (P 3))
                      ,      PrpF (P 7)  `Impl` PrpF (P 3) ] )
            ]) -- changelaw
  (fromList [("1", pure top), ("2", allsamebdd [P 7]), ("3", allsamebdd [P 7])]) -- agent 2 and 3 observe

type Story = (BelScene,[MultiEvent])

prisonSym :: Story
prisonSym = (prisonSymStart, map prisonSymInterview [2,1,3,1])
