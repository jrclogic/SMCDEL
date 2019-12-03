module SMCDEL.Examples.CherylDemo where

import Data.List

import SMCDEL.Explicit.DEMO_S5 as DEMO_S5

type MyWorld = (Int,Int,Int)

--  Cheryl: I have two younger brothers. The product of all our ages is 144.
allStates :: [MyWorld]
allStates = [ (c,b1,b2) | c  <- [1..144]
                        , b1 <- [1..(c-1)]
                        , b2 <- [1..(c-1)]
                        , c * b1 * b2 == 144 ]

start,step1,step2,step3,step4,step5 :: DEMO_S5.EpistM MyWorld

start = DEMO_S5.Mo states agents [] rels points where
  states = allStates
  agents = map DEMO_S5.Ag [1] -- a single observer agent
  rels = [ (DEMO_S5.Ag 1, [states]) ] -- nothing known
  points = allStates

cherylIs :: Int -> DemoForm MyWorld
cherylIs n = Disj [ Info (n,b1,b2) | b1 <- [1..144], b2 <- [1..144], (n,b1,b2) `elem` allStates ]

weKnowIt :: DemoForm MyWorld
weKnowIt = Disj [ Kn (Ag 1) (cherylIs n) | n <- [1..144]]

-- Albert: We still don't know your age. What other hints can you give us?
step1 = start `updPa` Ng weKnowIt

-- Cheryl: The sum of all our ages is the bus number of this bus that we are on.
step2 = updsPaW step1 [ sumIs n | n <- possibleSums ] where
  possibleSums = sort . nub $ map (\(c, b1, b2) -> c+b1+b2) allStates
  sumIs n = Disj (map Info (filter (\(c, b1, b2) -> c+b1+b2 == n) allStates))

-- Bernard: Of course we know the bus number, but we still don't know your age.
step3 = step2 `updPa` Ng weKnowIt

-- Cheryl: Oh, I forgot to tell you that my brothers have the same age.
step4 = step3 `updPa` broSame where
  broSame = Disj (map Info (filter (\(_, b1, b2) -> b1 == b2) allStates))

-- Albert and Bernard: Oh, now we know your age.
step5 = step4 `updPa` weKnowIt
