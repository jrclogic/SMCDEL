module SMCDEL.Examples.Prisoners where

import Data.HasCacBDD hiding (Top,Bot)

import SMCDEL.Explicit.S5
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5

n :: Int
n = 3

light :: Form
light = PrpF (P 0)

-- P 0 -- light is on
-- P i -- agent i has been in the room (and switched on the light)
-- agents: 1 is the counter, 2 and 3 are the others

prisonExpStart :: KripkeModelS5
prisonExpStart =
  KrMS5
    [1]
    [ ("1",[[1]]) ]
    [ (1, [(P k,False) | k <- [0..n] ] ) ]

prisonGoal :: Form
prisonGoal = K "1" $ Conj [ PrpF $ P k | k <- [1..n] ]

prisonAction :: ActionModelS5
prisonAction = ActMS5 actions actRels where
  p = PrpF . P
  actions =
    [ (0, (p 0      , [(P 0, Bot), (P 1, Top)]) ) -- interview 1 with light on
    , (1, (Neg (p 0), [            (P 1, Top)]) ) -- interview 1 with light off
    ]
    ++
    [ (k, (Top, [(P 0, p k `Impl` p 0), (P k, p 0 `Impl` p k)]) ) | k <- [2..n] ] -- interview k
  actRels = [ ("1", [[0],[1],[2..n]]) ]

prisonInterview :: Int -> MultipointedActionModelS5
prisonInterview 1 = (prisonAction, [0,1])
prisonInterview k = (prisonAction, [k])

data Story a b = Story a [b]

endOf :: (Update a b, Optimizable a) => Story a b -> a
endOf (Story start actions) =
  foldl (\cur a -> optimize (vocabOf start) $ cur `update` a) start actions

instance (Update a b, Optimizable a, TexAble a, TexAble b) => TexAble (Story a b) where
  tex (Story start actions) = adjust (tex start) ++ loop start actions where
    adjust thing = " \\raisebox{-.5\\height}{ \\begin{adjustbox}{max height=4cm, max width=0.3\\linewidth} $ " ++ thing ++ " $ \\end{adjustbox} } "
    loop _       []     = ""
    loop current (a:as) =
      let
        new = optimize (vocabOf start) $ current `update` a
      in
        " \\times " ++ adjust (tex a) ++ " = " ++ adjust (tex new) ++ "\\] \\[ " ++ loop new as

prisonExpStory :: Story PointedModelS5 MultipointedActionModelS5
prisonExpStory = Story (prisonExpStart,1) (map prisonInterview [2,1,3,1])

prisonSymStart :: MultipointedKnowScene
prisonSymStart = (KnS (map P [0..n]) law obs, actualStatesBdd) where
  law    = boolBddOf (Conj (Neg light : [ Neg $ wasInterviewed k | k <- [1..n] ]))
  obs    = [ ("1", []) ]
  actualStatesBdd = top

wasInterviewed, isNowInterviewed :: Int -> Form
wasInterviewed     = PrpF . P
isNowInterviewed k = PrpF (P (k + n))

lightSeenByOne :: Form
lightSeenByOne  = PrpF (P (1 + (2*n)))

prisonSymEvent :: KnowTransformer
prisonSymEvent = KnTrf -- agent 1 is interviewed
  (map P $ [ k+n | k <- [1..n] ] ++ [1+(2*n)] ) -- distinguish events
  (Conj [ isNowInterviewed 1 `Impl` (lightSeenByOne `Equi` light)
        , Disj [ Conj $ isNowInterviewed k : [Neg $ isNowInterviewed l | l <- [1..n], l /= k ] | k <- [1..n]]
        ] )
  -- light might be switched and visits of the agents might be recorded
  ( [ (P 0, boolBddOf $
          Conj $ isNowInterviewed 1 `Impl` Bot -- 1 turns off the light
               : concat [ [ Conj [Neg $ wasInterviewed k, isNowInterviewed k] `Impl` Top
                          , Conj [      wasInterviewed k, isNowInterviewed k] `Impl` light ]
                        | k <- [2..n] ])
  , (P 1, boolBddOf $ Disj [wasInterviewed 1, Conj [           isNowInterviewed 1]])
  ]
  ++
  [ (P k, boolBddOf $ Disj [wasInterviewed k, Conj [Neg light, isNowInterviewed k]])
  | k <- [2..n] ] )
  -- agent 1 observes whether they are interviewed, and if so, also observes the light
  [ ("1", let (PrpF px, PrpF py) = (isNowInterviewed 1, lightSeenByOne) in [px, py]) ]

prisonSymInterview :: Int -> MultipointedEvent
prisonSymInterview k = (prisonSymEvent, boolBddOf (isNowInterviewed k))

prisonSymStory :: Story MultipointedKnowScene MultipointedEvent
prisonSymStory = Story prisonSymStart (map prisonSymInterview [2,1,3,1])
