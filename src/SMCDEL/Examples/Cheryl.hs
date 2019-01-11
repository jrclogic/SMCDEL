module SMCDEL.Examples.Cheryl where

import Data.List

import SMCDEL.Language
import SMCDEL.Symbolic.S5

type Possibility = (Int, String)

possibilities :: [Possibility]
possibilities =
  [ (15,"May"), (16,"May"), (19,"May")
  , (17,"June"), (18,"June")
  , (14,"July"), (16,"July")
  , (14,"August"), (15,"August"), (17,"August") ]

dayIs :: Int -> Prp
dayIs = P

monthIs :: String -> Prp
monthIs "May"    = P 5
monthIs "June"   = P 6
monthIs "July"   = P 7
monthIs "August" = P 8
monthIs _        = undefined

thisPos :: Possibility -> Form
thisPos (d,m) = Conj $
  (PrpF (dayIs d) : [ Neg (PrpF $ dayIs d') | d' <- nub (map fst possibilities) \\ [d] ]) ++
  (PrpF (monthIs m) : [ Neg (PrpF $ monthIs m') | m' <- nub (map snd possibilities) \\ [m] ])

knWhich :: Agent -> Form
knWhich i = Disj [ K i (thisPos pos) | pos <- possibilities ]

start :: KnowStruct
start = KnS allprops statelaw obs where
  allprops = sort $ nub $ map (dayIs . fst) possibilities ++ map (monthIs . snd) possibilities
  statelaw = boolBddOf $ Conj
    [ Disj (map thisPos possibilities)
    , Conj [ Neg $ Conj [thisPos p1, thisPos p2] | p1 <- possibilities, p2 <- possibilities, p1 /= p2 ] ]
  obs = [ ("Albert", nub $ map (dayIs   . fst) possibilities)
        , ("Bernard", nub $ map (monthIs . snd) possibilities) ]

round1,round2,round3 :: KnowStruct
round1 = update start (Conj [Neg $ knWhich "Albert", K "Albert" $ Neg (knWhich "Bernard")])
round2 = update round1 (knWhich "Bernard")
round3 = update round2 (knWhich "Albert")

cherylsBirthday :: String
cherylsBirthday = m ++ " " ++ show d ++ "th" where
  [(d,m)] = filter (\(d',m') -> [monthIs m', dayIs d'] `elem` statesOf round3) possibilities
