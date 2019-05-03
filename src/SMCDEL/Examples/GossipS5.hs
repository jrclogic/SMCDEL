module SMCDEL.Examples.GossipS5 where

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import Data.List ((\\))

gossipers :: Int -> [Int]
gossipers n = [0..(n-1)]

hasSof :: Int -> Int -> Int -> Prp
hasSof n a b | a == b    = error "Let's not even talk about that."
             | otherwise = toEnum (n * a + b)

has :: Int -> Int -> Int -> Form
has n a b = PrpF (hasSof n a b)

expert :: Int -> Int -> Form
expert n a = Conj [ PrpF (hasSof n a b) | b <- gossipers n, a /= b ]

allExperts :: Int -> Form
allExperts n = Conj [ expert n a | a <- gossipers n ]

gossipInit :: Int -> KnowScene
gossipInit n = (KnS vocab law obs, actual) where
  vocab  = [ hasSof n i j | i <- gossipers n, j <- gossipers n, i /= j ]
  law    = boolBddOf $ Conj [ Neg $ PrpF $ hasSof n i j
                            | i <- gossipers n, j <- gossipers n, i /= j]
  obs    = [ (show i, []) | i <- gossipers n ]
  actual = [ ]

thisCallProp :: (Int,Int) -> Prp
thisCallProp (i,j) | i < j     = P (100 + 10*i + j)
                   | otherwise = error $ "wrong call: " ++ show (i,j)

call :: Int -> (Int,Int) -> Event
call n (a,b) = (callTrf n, [thisCallProp (a,b)])

callTrf :: Int -> KnowTransformer
callTrf n = KnTrf eventprops eventlaw changelaws eventobs where
  thisCallHappens (i,j) = PrpF $ thisCallProp (i,j)
  isInCallForm k = Disj $ [ thisCallHappens (i,k) | i <- gossipers n \\ [k], i < k ]
                       ++ [ thisCallHappens (k,j) | j <- gossipers n \\ [k], k < j ]
  allCalls = [ (i,j) | i <- gossipers n, j <- gossipers n, i < j ]
  eventprops = map thisCallProp allCalls
  eventlaw = simplify $
    Conj [ Disj (map thisCallHappens allCalls)
         -- some call must happen, but never two at the same time:
         , Neg $ Disj [ Conj [thisCallHappens c1, thisCallHappens c2]
                      | c1 <- allCalls, c2 <- allCalls \\ [c1] ] ]
  callPropsWith k = [ thisCallProp (i,k) | i <- gossipers n, i < k ]
                 ++ [ thisCallProp (k,j) | j <- gossipers n, k < j ]
  eventobs = [(show k, callPropsWith k) | k <- gossipers n]
  changelaws =
    [(hasSof n i j, boolBddOf $              -- after a call, i has the secret of j iff
        Disj [ has n i j                     -- i already knew j, or
             , Conj (map isInCallForm [i,j]) -- i and j are both in the call or
             , Conj [ isInCallForm i         -- i is in the call and there is some k in
                    , Disj [ Conj [ isInCallForm k, has n k j ] -- the call who knew j
                           | k <- gossipers n \\ [j] ] ]
             ])
    | i <- gossipers n, j <- gossipers n, i /= j ]

doCall :: KnowScene -> (Int,Int) -> KnowScene
doCall start (a,b) = start `update` call (length $ agentsOf start) (a,b)

after :: Int -> [(Int,Int)] -> KnowScene
after n = foldl doCall (gossipInit n)

isSuccess :: Int -> [(Int,Int)] -> Bool
isSuccess n cs = evalViaBdd (after n cs) (allExperts n)

whoKnowsMeta :: KnowScene -> [(Int,[(Int,String)])]
whoKnowsMeta scn = [ (k, map (meta k) [0..maxid] ) | k <- [0..maxid] ] where
  n = length (agentsOf scn)
  maxid = n - 1
  meta x y = (y, map (knowsAbout x y) [0..maxid])
  knowsAbout x y i
    | y == i = 'X'
    | evalViaBdd scn (      K (show x) $       PrpF (hasSof n y i)) = 'Y'
    | evalViaBdd scn (Neg $ K (show x) $ Neg $ PrpF (hasSof n y i)) = '?'
    | evalViaBdd scn (      K (show x) $ Neg $ PrpF (hasSof n y i)) = '_'
    | otherwise                                                     = 'E'

allSequs :: Int -> Int -> [ [(Int,Int)] ]
allSequs _ 0 = [ [] ]
allSequs n l = [ (i,j):rest | rest <- allSequs n (l-1), i <- gossipers n, j <- gossipers n, i < j ]
