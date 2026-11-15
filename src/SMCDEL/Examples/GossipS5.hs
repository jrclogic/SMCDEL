{- |

__Atomic-knowing Gossip on knowledge structures with factual change__

This module models the same gossip problem as in "SMCDEL.Examples.GossipKw", but differently.
Agent \(a\) knows the secret of (b\) iff the atomic proposition \(S_a b\) is true.
Learning of secrets is then modeled as factual change.

Again we only consider the classic, static version of the gossip problem
where \(N\) is a total graph and thus everyone can call everyone.

Most functions here take a parameter \(n\) for the number of agents.
The definitions are only correct for n up to 9 because of how we
define the proposition letters in `thisCallProp` and `receives`.

-}

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
has n a b = if a == b then Top else PrpF (hasSof n a b)

expert :: Int -> Int -> Form
expert n a = Conj [ has n a b | b <- gossipers n ]

allExperts :: Int -> Form
allExperts n = Conj [ expert n a | a <- gossipers n ]

gossipInit :: Int -> MultipointedKnowScene
gossipInit n = (KnS vocab law obs, curLaw) where
  vocab  = [ hasSof n i j | i <- gossipers n, j <- gossipers n, i /= j ]
  law    = boolBddOf $ Conj [ Neg $ PrpF $ hasSof n i j
                            | i <- gossipers n, j <- gossipers n, i /= j]
  obs    = [ (show i, []) | i <- gossipers n ]
  curLaw = boolBddOf Top

-- | Here (i,j) with i<j says that the call i-to-j or j-to-i happens.
thisCallProp :: (Int,Int) -> Prp
thisCallProp (i,j) | i < j     = P (100 + 10*i + j)
                   | otherwise = error $ "wrong call: " ++ show (i,j)

allCalls :: Int -> [(Int, Int)]
allCalls n = [ (i,j) | i <- gossipers n, j <- gossipers n, i < j ]

-- | Here (i,j) says that i receives the secret of j from the other agent in the call.
receives :: (Int,Int) -> Prp
receives (i,j) = P (200 + 10*i + j)

callTrf :: Int -> KnowTransformer
callTrf n = KnTrf eventprops eventlaw changelaws eventobs where
  thisCallHappens (i,j) = PrpF $ thisCallProp (i,j)
  eventprops = map thisCallProp (allCalls n)
            ++ [ receives (i,j) | i <- gossipers n, j <- gossipers n ]
  eventlaw = simplify $
    Conj [ Disj (map thisCallHappens (allCalls n))
         -- some call must happen, but never two at the same time:
         , Neg $ Disj [ Conj [thisCallHappens c1, thisCallHappens c2]
                      | c1 <- allCalls n, c2 <- allCalls n \\ [c1] ]
         -- i receives secret j iff some call i,k or k,i happens and k has j:
         , Conj [ PrpF (receives (i,j)) `Equi`
                    Disj [ thisCallHappens (if i < k then (i,k) else (k,i)) `conj` has n k j
                         | k <- gossipers n \\ [i] ]
                | i <- gossipers n, j <- gossipers n ]
         ]
  callPropsWith k = [ thisCallProp (i,k) | i <- gossipers n, i < k ]
                 ++ [ thisCallProp (k,j) | j <- gossipers n, k < j ]
  receivePropsWith k = [ receives (k,i) | i <- gossipers n ]
  eventobs = [(show k, callPropsWith k ++ receivePropsWith k) | k <- gossipers n]
  changelaws =
    [(hasSof n i j, boolBddOf $              -- after a call, i has the secret of j iff
        Disj [ has n i j                     -- i already knew j, or
             , PrpF (receives (i,j))         -- receives it
             ])
    | i <- gossipers n, j <- gossipers n, i /= j ]

call :: Int -> (Int,Int) -> MultipointedEvent
call n (a,b) = (callTrf n, [thisCallProp (a,b)] `booloutof` map thisCallProp (allCalls n))

doCall :: MultipointedKnowScene -> (Int,Int) -> MultipointedKnowScene
doCall start (a,b) = start `update` call (length $ agentsOf start) (a,b)

after :: Int -> [(Int,Int)] -> MultipointedKnowScene
after n = foldl doCall (gossipInit n)

isSuccess :: Int -> [(Int,Int)] -> Bool
isSuccess n cs = after n cs |= allExperts n

whoKnowsMeta :: MultipointedKnowScene -> [(Int,[(Int,String)])]
whoKnowsMeta scn = [ (k, map (meta k) [0..maxid] ) | k <- [0..maxid] ] where
  n = length (agentsOf scn)
  maxid = n - 1
  meta x y = (y, map (knowsAbout x y) [0..maxid])
  knowsAbout x y i
    | y == i = 'X'
    | scn |=      K (show x) (       PrpF (hasSof n y i)) = 'Y'
    | scn |= Neg (K (show x) $ Neg $ PrpF (hasSof n y i)) = '?'
    | scn |=      K (show x) ( Neg $ PrpF (hasSof n y i)) = '_'
    | otherwise                                                     = 'E'

allSequs :: Int -> Int -> [ [(Int,Int)] ]
allSequs _ 0 = [ [] ]
allSequs n l = [ (i,j):rest | rest <- allSequs n (l-1), i <- gossipers n, j <- gossipers n, i < j ]

{- $
For example, among three agents, after a call the non-involved agent
still knows who knows what:

>>> mapM_ print (whoKnowsMeta (after 3 [(0,1)]))
(0,[(0,"XY_"),(1,"YX_"),(2,"__X")])
(1,[(0,"XY_"),(1,"YX_"),(2,"__X")])
(2,[(0,"XY_"),(1,"YX_"),(2,"__X")])

This is different for four agents, where the two non-involved agents
are unsure which call happened:

>>> mapM_ print (whoKnowsMeta (after 4 [(0,1)]))
(0,[(0,"XY__"),(1,"YX__"),(2,"__X_"),(3,"___X")])
(1,[(0,"XY__"),(1,"YX__"),(2,"__X_"),(3,"___X")])
(2,[(0,"X?_?"),(1,"?X_?"),(2,"__X_"),(3,"??_X")])
(3,[(0,"X??_"),(1,"?X?_"),(2,"??X_"),(3,"___X")])

However, when involved in a second call, an agent can learn
who else must have learned something in the first call

>>> after 4 [(0,1),(1,2)] |= K "2" (has 4 0 1)
True

After three calls, an agent only in the last call does not
know for sure what the first two calls were:

>>> after 4 [(0,1),(1,2),(2,3)] |= K "3" (has 4 1 2)
False

But agent 3 still knows that "1 has 2 or 0 has 2":

>>> after 4 [(0,1),(1,2),(2,3)] |= K "3" (has 4 1 2 `disj` has 4 0 2)
True

-}
