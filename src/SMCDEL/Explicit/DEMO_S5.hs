-- Note: This is a modified version of DEMO-S5 by Jan van Eijck.
-- For the original, see http://homepages.cwi.nl/~jve/software/demo_s5/
module SMCDEL.Explicit.DEMO_S5 where

import Control.Arrow (first,second)
import Data.List (sortBy)

import SMCDEL.Internal.Help (apply,restrict,Erel,bl)

newtype Agent = Ag Int deriving (Eq,Ord,Show)

data DemoPrp = DemoP Int | DemoQ Int | DemoR Int | DemoS Int deriving (Eq,Ord)
instance Show DemoPrp where
  show (DemoP 0) = "p"; show (DemoP i) = "p" ++ show i
  show (DemoQ 0) = "q"; show (DemoQ i) = "q" ++ show i
  show (DemoR 0) = "r"; show (DemoR i) = "r" ++ show i
  show (DemoS 0) = "s"; show (DemoS i) = "s" ++ show i

data EpistM state = Mo
             [state]
             [Agent]
             [(state,[DemoPrp])]
             [(Agent,Erel state)]
             [state]  deriving (Eq)

instance Show state => Show (EpistM state) where
  show (Mo worlds ags val accs points) = concat
    [ "Mo\n  "
    , show worlds, "\n  "
    , show ags, "\n  "
    , show val, "\n  "
    , show accs, "\n  "
    , show points, "\n"
    ]

rel :: Show a => Agent -> EpistM a -> Erel a
rel ag (Mo _ _ _ rels _) = apply rels ag

initM :: (Num state, Enum state) => [Agent] -> [DemoPrp] -> EpistM state
initM ags props = Mo worlds ags val accs points where
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

data DemoForm a = Top
            | Info a
            | Prp DemoPrp
            | Ng (DemoForm a)
            | Conj [DemoForm a]
            | Disj [DemoForm a]
            | Kn Agent (DemoForm a)
            | PA (DemoForm a) (DemoForm a)
            | PAW (DemoForm a) (DemoForm a)
          deriving (Eq,Ord,Show)

impl :: DemoForm a -> DemoForm a -> DemoForm a
impl form1 form2 = Disj [Ng form1, form2]

-- | semantics: truth at a world in a model
isTrueAt :: (Show state, Ord state) => EpistM state -> state -> DemoForm state -> Bool
isTrueAt _ _ Top = True
isTrueAt _ w (Info x) = w == x
isTrueAt (Mo _ _ val _ _) w (Prp p) = p `elem` apply val w
isTrueAt m w (Ng f) = not (isTrueAt m w f)
isTrueAt m w (Conj fs) = all (isTrueAt m w) fs
isTrueAt m w (Disj fs) = any (isTrueAt m w) fs
isTrueAt m w (Kn ag f) = all (flip (isTrueAt m) f) (bl (rel ag m) w)
isTrueAt m w (PA f g) = not (isTrueAt m w f) || isTrueAt (updPa m f) w g
isTrueAt m w (PAW f g) = not (isTrueAt m w f) || isTrueAt (updPaW m f) w g

-- | global truth in a model
isTrue :: Show a => Ord a => EpistM a -> DemoForm a -> Bool
isTrue m@(Mo _ _ _ _ points) f = all (\w -> isTrueAt m w f) points

-- | public announcement
updPa :: (Show state, Ord state) => EpistM state -> DemoForm state -> EpistM state
updPa m@(Mo states agents val rels actual) f = Mo states' agents val' rels' actual' where
  states' = [ s | s <- states, isTrueAt m s f ]
  val'    = [ (s, ps) | (s,ps) <- val, s `elem` states' ]
  rels'   = [ (ag,restrict states' r) | (ag,r) <- rels ]
  actual' = [ s | s <- actual, s `elem` states' ]

updsPa ::  (Show state, Ord state) => EpistM state -> [DemoForm state] -> EpistM state
updsPa = foldl updPa

-- | public announcement-whether
updPaW :: (Show state, Ord state) => EpistM state -> DemoForm state -> EpistM state
updPaW m@(Mo states agents val rels actual) f = Mo states agents val rels' actual where
  rels'    = [ (ag, sortL $ concatMap split r) | (ag,r) <- rels ]
  split ws = filter (/= []) [ filter (\w -> isTrueAt m w f) ws, filter (\w -> not $ isTrueAt m w f) ws ]

updsPaW ::  (Show state, Ord state) => EpistM state -> [DemoForm state] -> EpistM state
updsPaW = foldl updPaW

-- | safe substitutions
sub :: Show a => [(DemoPrp,DemoForm a)] -> DemoPrp -> DemoForm a
sub subst p | p `elem` map fst subst = apply subst p
            | otherwise              = Prp p

-- | public factual change
updPc :: (Show state, Ord state) => [DemoPrp] -> EpistM state -> [(DemoPrp,DemoForm state)] -> EpistM state
updPc ps m@(Mo states agents _ rels actual) sb = Mo states agents val' rels actual where
   val' = [ (s, [p | p <- ps, isTrueAt m s (sub sb p)]) | s <- states ]

updsPc :: Show state => Ord state => [DemoPrp] -> EpistM state
                     -> [[(DemoPrp,DemoForm state)]] -> EpistM state
updsPc ps = foldl (updPc ps)

updPi :: (state1 -> state2) -> EpistM state1 -> EpistM state2
updPi f (Mo states agents val rels actual) =
  Mo
  (map f states)
  agents
  (map (first f) val)
  (map (second (map (map f))) rels)
  (map f actual)

bTables :: Int -> [[Bool]]
bTables 0 = [[]]
bTables n = map (True:) (bTables (n-1)) ++ map (False:) (bTables (n-1))

initN :: Int -> EpistM [Bool]
initN n = Mo states agents [] rels points where
  states = bTables n
  agents = map Ag [1..n]
  rels = [(Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- bTables (i-1),
                   tab2 <- bTables (n-i) ]) | i <- [1..n] ]
  points = [False: replicate (n-1) True]

fatherN :: Int -> DemoForm [Bool]
fatherN n = Ng (Info (replicate n False))

kn :: Int -> Int -> DemoForm [Bool]
kn n i = Disj [Kn (Ag i) (Disj [ Info (tab1++[True]++tab2)
                               | tab1 <- bTables (i-1)
                               , tab2 <- bTables (n-i)
                               ] ),
               Kn (Ag i) (Disj [ Info (tab1++[False]++tab2)
                               | tab1 <- bTables (i-1)
                               , tab2 <- bTables (n-i)
                               ] )
              ]

dont :: Int -> DemoForm [Bool]
dont n = Conj [Ng (kn n i) | i <- [1..n] ]

knowN :: Int -> DemoForm [Bool]
knowN n = Conj [kn n i | i <- [2..n] ]

solveN :: Int -> EpistM [Bool]
solveN n = updsPa (initN n) (f:istatements ++ [knowN n]) where
  f = fatherN n
  istatements = replicate (n-2) (dont n)
