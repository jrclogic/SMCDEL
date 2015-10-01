-- Note: This is a slightly modified version of DEMO-S5 by Jan van Eijck
-- which can be found at http://homepages.cwi.nl/~jve/software/demo_s5/
module DEMO_S5 where
import Control.Arrow (first,second)
import Data.List (sortBy)
import HELP (apply,restrict,Erel,bl)

data Agent = Ag Int deriving (Eq,Ord,Show)

data Prp = P Int | Q Int | R Int | S Int deriving (Eq,Ord)
instance Show Prp where
  show (P 0) = "p"; show (P i) = "p" ++ show i
  show (Q 0) = "q"; show (Q i) = "q" ++ show i
  show (R 0) = "r"; show (R i) = "r" ++ show i
  show (S 0) = "s"; show (S i) = "s" ++ show i

data EpistM state = Mo
             [state]
             [Agent]
             [(state,[Prp])]
             [(Agent,Erel state)]
             [state]  deriving (Eq,Show)

rel :: Show a => Agent -> EpistM a -> Erel a
rel ag (Mo _ _ _ rels _) = apply rels ag

initM :: (Num state, Enum state) =>
         [Agent] -> [Prp] -> EpistM state
initM ags props = Mo worlds ags val accs points
  where
    worlds  = [0..(2^k-1)]
    k       = length props
    val     = zip worlds (sortL (powerList props))
    accs    = [ (ag,[worlds]) | ag  <- ags        ]
    points  = worlds

powerList  :: [a] -> [[a]]
powerList  [] = [[]]
powerList  (x:xs) =
  powerList xs ++ map (x:) (powerList xs)

sortL :: Ord a => [[a]] -> [[a]]
sortL  = sortBy
  (\ xs ys -> if length xs < length ys
                then LT
              else if length xs > length ys
                then GT
              else compare xs ys)

data Form a = Top
            | Info a
            | Prp Prp
            | Ng (Form a)
            | Conj [Form a]
            | Disj [Form a]
            | Kn Agent (Form a)
          deriving (Eq,Ord,Show)

impl :: Form a -> Form a -> Form a
impl form1 form2 = Disj [Ng form1, form2]

isTrueAt :: Show state => Ord state =>
            EpistM state -> state -> Form state -> Bool
isTrueAt _ _ Top = True
isTrueAt _ w (Info x) = w == x
isTrueAt
  (Mo _ _ val _ _) w (Prp p) = let
   props = apply val w
  in
   elem p props
isTrueAt m w (Ng f) = not (isTrueAt m w f)
isTrueAt m w (Conj fs) = all (isTrueAt m w) fs
isTrueAt m w (Disj fs) = any (isTrueAt m w) fs
isTrueAt m w (Kn ag f) = let
    r = rel ag m
    b = bl r w
  in
    all (flip (isTrueAt m) f) b

isTrue :: Show a => Ord a => EpistM a -> Form a -> Bool
isTrue m@(Mo _ _ _ _ points) f =
  all (\w -> isTrueAt m w f) points

updPa :: Show state => Ord state =>
          EpistM state -> Form state -> EpistM state
updPa m@(Mo states agents val rels actual) f = Mo states' agents val' rels' actual'
   where
   states' = [ s | s <- states, isTrueAt m s f ]
   val'    = [ (s, ps) | (s,ps) <- val, s `elem` states' ]
   rels'   = [(ag,restrict states' r) | (ag,r) <- rels ]
   actual' = [ s | s <- actual, s `elem` states' ]

updsPa ::  Show state => Ord state =>
            EpistM state -> [Form state] -> EpistM state
updsPa = foldl updPa

sub :: Show a => Eq a => [(Prp,Form a)] -> Prp -> Form a
sub subst p =
  if p `elem` map fst subst
    then apply subst p
    else Prp p

updPc :: Show state => Ord state => [Prp] -> EpistM state
                    -> [(Prp,Form state)] -> EpistM state
updPc ps m@(Mo states agents _ rels actual) sb =
  Mo states agents val' rels actual
   where
   val' = [ (s, [p | p <- ps, isTrueAt m s (sub sb p)])
                                          | s <- states ]

updsPc :: Show state => Ord state => [Prp] -> EpistM state
                     -> [[(Prp,Form state)]] -> EpistM state
updsPc ps = foldl (updPc ps)

updPi :: (state -> state) -> EpistM state -> EpistM state
updPi f (Mo states agents val rels actual) =
  Mo
  (map f states)
  agents
  (map (first f) val)
  (map (second (map (map f))) rels)
  (map f actual)

bTables :: Int -> [[Bool]]
bTables 0 = [[]]
bTables n = map (True:) (bTables (n-1))
            ++ map (False:) (bTables (n-1))

initN :: Int -> EpistM [Bool]
initN n = Mo states agents [] rels points where
  states = bTables n
  agents = map Ag [1..n]
  rels = [(Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- bTables (i-1),
                   tab2 <- bTables (n-i) ]) | i <- [1..n] ]
  points = [False: replicate (n-1) True]

fatherN :: Int -> Form [Bool]
fatherN n = Ng (Info (replicate n False))

kn :: Int -> Int -> Form [Bool]
kn n i = Disj [Kn (Ag i) (Disj [Info (tab1++[True]++tab2) |
                        tab1 <- bTables (i-1),
                        tab2 <- bTables (n-i) ]),
               Kn (Ag i) (Disj [Info (tab1++[False]++tab2) |
                        tab1 <- bTables (i-1),
                        tab2 <- bTables (n-i) ])]

dont :: Int -> Form [Bool]
dont n = Conj [Ng (kn n i) | i <- [1..n] ]

knowN :: Int -> Form [Bool]
knowN n = Conj [kn n i | i <- [2..n] ]

solveN :: Int -> EpistM [Bool]
solveN n = updsPa (initN n) (f:istatements ++ [knowN n])
  where
  f = fatherN n
  istatements = replicate (n-2) (dont n)
