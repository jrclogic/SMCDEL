module SMCDEL.Examples.Cheryl where

import Data.HasCacBDD (Bdd,con,disSet)
import Data.List

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Internal.Help (powerset)

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
  obs = [ ("Albert" , nub $ map (monthIs . snd) possibilities)
        , ("Bernard", nub $ map (dayIs   . fst) possibilities) ]

round1,round2,round3 :: KnowStruct
round1 = update start (Conj [Neg $ knWhich "Albert", K "Albert" $ Neg (knWhich "Bernard")])
round2 = update round1 (knWhich "Bernard")
round3 = update round2 (knWhich "Albert")

cherylsBirthday :: String
cherylsBirthday = m ++ " " ++ show d ++ "th" where
  [(d,m)] = filter (\(d',m') -> [monthIs m', dayIs d'] `elem` statesOf round3) possibilities

newtype Variable = Var [Prp] deriving (Eq,Ord,Show)

bitsOf :: Int -> [Int]
bitsOf 0 = []
bitsOf n = k : bitsOf (n - 2^k) where
  k :: Int
  k = floor (logBase 2 (fromIntegral n) :: Double)

-- alternative to:  booloutofForm (powerset props !! n) props
is :: Variable -> Int -> Form
is (Var props) n = Conj [ (if i `elem` bitsOf n then id else Neg) (PrpF k)
                        | (k,i) <- zip props [(0::Int)..] ]

isBdd :: Variable -> Int -> Bdd
isBdd v = boolBddOf . is v

-- inverse of "is":
valueIn :: Variable -> State -> Int
valueIn (Var props) s = sum [ 2^i | (k,i) <- zip props [(0::Int)..], k `elem` s ]

explainState :: [Variable] -> State -> [Int]
explainState vs s = map (`valueIn` s) vs

-- an agent knows the value iff they know-whether all bits
kv :: Agent -> Variable -> Form
kv i (Var props) = Conj [ Kw i (PrpF k) | k <- props ]

--  Cheryl: I have two younger brothers. The product of all our ages is 144.
allStates :: [(Int,Int,Int)]
allStates = [ (c,b1,b2) | c  <- [1..144]
                        , b1 <- [1..(c-1)]
                        , b2 <- [1..(c-1)]
                        , c * b1 * b2 == 144 ]

cheryl, broOne :: Variable
cheryl = Var [P (2*k   ) | k <- [0..7] ]
broOne = Var [P (2*k +1) | k <- [0..7] ]

ageKnsStart :: KnowStruct
ageKnsStart = KnS allprops statelaw obs where
  allprops = let (Var cs, Var bs) = (cheryl, broOne) in sort $ cs ++ bs
  statelaw = disSet [ con (cheryl `isBdd` c) (broOne `isBdd` b) | (c,b,_) <- allStates ]
  obs = [("albernard",[])]

step1,step2,step3,step4,step5 :: KnowStruct

-- Albert: We still don't know your age. What other hints can you give us?
step1 = ageKnsStart `update` Neg (kv "albernard" cheryl)

-- Cheryl: The sum of all our ages is the bus number of this bus that we are on.
step2 = step1 `update` revealTransformer
-- For this we need a way to reveal the sum, hence we use a knowledge transformer
revealTransformer :: KnowTransformer
revealTransformer = noChange KnTrf addProps addLaw addObs where
  addProps = map P [1001..1008] -- 8 bits to label all sums
  addLaw = simplify $ Conj [ Disj [ label (c + b + a) | (c,b,a) <- allStates ]
                           , Conj [ sumIs s `Equi` label s | s <- [1..144] ] ] where
    label s = booloutofForm (powerset (map P [1001..1008]) !! s) (map P [1001..1008])
    sumIs n = Disj [ Conj [ cheryl `is` c, broOne `is` b ]
                   | (c,b,a) <- allStates, c + b + a == n ]
  addObs = [("albernard",addProps)]

-- Bernard: Of course we know the bus number, but we still don't know your age.
step3 = step2 `update` Neg (kv "albernard" cheryl)

-- Cheryl: Oh, I forgot to tell you that my brothers have the same age.
step4 = step3 `update` sameAge where
  sameAge = Disj [ Conj [cheryl `is` c, broOne `is` b ]
                 | (c,b,a) <- allStates
                 , b == a ]

-- Albert and Bernard: Oh, now we know your age.
step5 = step4 `update` kv "albernard" cheryl
