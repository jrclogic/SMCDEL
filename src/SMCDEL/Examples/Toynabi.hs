module SMCDEL.Examples.Toynabi where

import Data.List ((\\),sort)

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Explicit.S5
import SMCDEL.Translations.S5
import SMCDEL.Other.Planning

-- | Given nPlayers and nCards in total, this proposition encodes that player i has card c in position p.
-- Note that we start counting players with 1, but cards and positions with 0.
cardIsAt :: Int -> Int -> Int -> Int -> Int -> Prp
cardIsAt nPlayers nCards i c p = P ((i * nCards * nPositions) + (c * nPositions) + p) where
  nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)

-- | A proposition to say that the card c should be played next.
toPlay :: Int -> Int -> Int -> Prp
toPlay nPlayers nCards c = toEnum . (+(1+c)) . fromEnum $ cardIsAt nPlayers nCards nPlayers (nCards-1) (nPositions-1) where
  nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)

-- | This proposition says that the game has ended.
done :: Int -> Int -> Prp
done nPlayers nCards = toPlay nPlayers nCards nCards

-- | Print and translate the vocabulary in both directions, just for debugging.
vocab :: Int -> Int -> IO ()
vocab nPlayers nCards = do
  mapM_ printExplain (vocabOf $ toynabiStartFor nPlayers nCards)
  putStrLn "--"
  mapM_ putStrLn [ show i ++ " has " ++ show c ++ " @ " ++ show p ++ "\t " ++ show (cardIsAt nPlayers nCards i c p) | i <- players, c <- cards, p <- positions ]
  mapM_ putStrLn [ "toPlay: " ++ show c ++ "\t" ++ show (toPlay nPlayers nCards c) | c <- cards ]
  mapM_ putStrLn [ "done! \t" ++ show (toPlay nPlayers nCards nCards) ]
  where
    printExplain p = putStrLn $ show p ++ "\t" ++ explain nPlayers nCards p
    players = [1..nPlayers]
    cards = [0..(nCards-1)]
    nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)
    positions = [0..(nPositions-1)]

explain :: Int -> Int -> Prp -> String
explain nPlayers nCards (P k)
  | P k == toPlay nPlayers nCards nCards = "done!"
  | P k >= toPlay nPlayers nCards 0 = "to play: " ++ show (k +1 - fromEnum (toPlay nPlayers nCards 1)) -- TODO test and check this!
  | otherwise = show i ++ " has " ++ show c ++ " @ " ++ show p where
      nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)
      i = k `div` (nCards * nPositions)
      c = (k - (i * nCards * nPositions)) `div` nPositions
      p = k - (i * nCards * nPositions) - (c * nPositions)

explainState :: Int -> Int -> State -> String
explainState nPlayers nCards state = show [  [ c | p <- positions, c <- cards, cardIsAt nPlayers nCards i c p `elem` state  ] | i <- players ] ++ tP where
  players = [1..nPlayers]
  cards = [0..(nCards-1)]
  nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)
  positions = [0..(nPositions-1)]
  tP = concat $ [ " to play: " ++ show c | c <- cards, toPlay nPlayers nCards c `elem` state ]
             ++ [ "done!" | toPlay nPlayers nCards nCards `elem` state ]

-- | The starting knowledge structure.
toynabiStartFor :: Int -> Int -> MultipointedKnowScene
toynabiStartFor nPlayers nCards = (KnS voc law obs, cur) where
  players = [1..nPlayers]
  cards = [0..(nCards-1)]
  nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)
  positions = [0..(nPositions-1)]
  voc = sort $ [ cardIsAt nPlayers nCards i c p | i <- players, c <- cards, p <- positions  ]
            ++ [ toPlay nPlayers nCards c | c <- cards ]
            ++ [ done nPlayers nCards ]
  law = boolBddOf $ Conj $
    -- The next card to be played is 0:
       [ (if c==0 then id else Neg) $ PrpF $ toPlay nPlayers nCards c | c <- cards ++ [nCards] ]
    -- Each card must be at someone in some position, but not two:
    ++ [ Disj [ PrpF $ cardIsAt nPlayers nCards i c p | i <- players, p <- positions ] | c <- cards ]
    ++ [ Neg $ Conj [ PrpF $ cardIsAt nPlayers nCards i c p
                    , PrpF $ cardIsAt nPlayers nCards j c q ] | c <- cards
                                                              , i <- players, j <- players
                                                              , p <- positions, q <- positions
                                                              , i /= j || p /= q ]
    -- For each player each position can only hold one card:
    ++ [ Neg $ Conj [ PrpF $ cardIsAt nPlayers nCards i c p
                    , PrpF $ cardIsAt nPlayers nCards i d p ] | c <- cards, d <- cards
                                                              , c /= d
                                                              , i <- players
                                                              , p <- positions ]
    -- If nPlayers * nPositions > nCards then there are empty positions:
    ++ [ Conj [ Neg $ PrpF $ cardIsAt nPlayers nCards i c p ] | (i,p) <- drop nCards [ (i,p) | i <- players, p <- positions ], c <- cards ]
  obs = [ (show i, voc \\ [ cardIsAt nPlayers nCards i c p | c <- cards, p <- positions ]) | i <- players ]
  cur = boolBddOf $ Conj $
          -- distribute all the cards:
          [ PrpF $ cardIsAt nPlayers nCards i c p | (c,(i,p)) <- zip cards [ (i,p) | i <- players, p <- positions ] ] ++
          -- set toPlay to 0:
          [ (if c == 0 then id else Neg) $ PrpF $ toPlay nPlayers nCards c | c <- cards ]

-- | Tell agent i that they have card c at position p.
tell :: Int -> Int -> Int -> Int -> Int -> Labelled MultipointedEvent
tell nPlayers nCards i c p = (label, (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top)) where
  label       = "tell " ++ show i ++ " card " ++ show c ++ " @ " ++ show p
  addprops    = [ ]
  addlaw      = PrpF $ cardIsAt nPlayers nCards i c p
  changeLaw   = [ ]
  addObs      = [ (show j, []) | j <- players ]
  players     = [1..nPlayers]

-- | Let agent i play the card at position p.
play :: Int -> Int -> Int -> Int -> Labelled MultipointedEvent
play nPlayers nCards i p = (label, (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top)) where
  label       = show i ++ " plays position " ++ show p
  addprops    = [ ]
  addlaw      = Disj [ Conj [ PrpF $ toPlay nPlayers nCards c
                            , PrpF $ cardIsAt nPlayers nCards i c p ]
                     | c <- cards ]
  changeLaw   = [ (cardIsAt nPlayers nCards i c p, boolBddOf Bot) | c <- cards ] -- remove card from that position
                ++ [ ( toPlay nPlayers nCards 0, boolBddOf $ ite (tP 0) Bot (tP 0) ) ] -- if first card is played
                ++ [ ( toPlay nPlayers nCards c, boolBddOf $ ite (tP c) Bot (ite (tP (c-1)) Top (tP c)) ) | c <- cards, c > 0 ] -- increase toPlay
                ++ [ ( toPlay nPlayers nCards nCards, boolBddOf $ ite (tP (nCards-1)) Top Bot ) | c <- cards, c > 0 ] -- set done

  addObs      = [ (show j, []) | j <- players ]
  players     = [1..nPlayers]
  tP c        = PrpF $ toPlay nPlayers nCards c
  cards       = [0..(nCards-1)]

-- | The goal.
toynabiGoal :: Int -> Int -> Form
toynabiGoal nPlayers nCards = PrpF $ done nPlayers nCards

-- | The whole cooperative planning task.
toynabi :: Int -> Int -> CoopTask MultipointedKnowScene MultipointedEvent
toynabi nPlayers nCards = CoopTask (toynabiStartFor nPlayers nCards) actions (toynabiGoal nPlayers nCards) where
  actions    = [ (show i, tell nPlayers nCards j c p) | i <- players, j <- players, i /= j, c <- cards, p <- positions  ] ++
               [ (show i, play nPlayers nCards i p) | i <- players, p <- positions ]
  players    = [1..nPlayers]
  cards      = [0..(nCards-1)]
  nPositions = ceiling (fromIntegral nCards / fromIntegral nPlayers :: Double)
  positions  = [0..(nPositions-1)]

-- | An example result to test whether updating works, translated to a Kripke model.
exampleResult :: PointedModelS5
exampleResult =  generatedSubmodel $ knsToKripke (fst theKNS, head $ statesOf $ fst theKNS) where
  theKNS = toynabiStartFor 2 4
    `update` snd (tell 2 4 1 0 0)
    `update` snd (play 2 4 1 0)
    `update` snd (play 2 4 1 1)
