

\begin{code}
module Main where
import Control.Monad
import Data.List
import Data.Maybe
import SMCDEL.Language
import SMCDEL.Other.NonS5
import Data.Map.Strict (fromList)
import SMCDEL.Symbolic.HasCacBDD (boolBddOf)
import Data.HasCacBDD hiding (Top,Bot)
\end{code}

A new try at Russian Cards.

Idea: $P_{2k}$ means that Alice has card k, $P_{2k+1}$ means that Bob has
it and both propositions being false means that Carol has it.
Note that this cuts the number of propositions to 2/3 of the previous amount
and simplifies the the state law to ensure that not both propositions about
the same card are true.

BUT this idea does not help, because we still need the third proposition to
describe the knowledge of Carol.

SO, we have to go back to three props.

OR use the general Non-S5 implementation where we do not need observational
variables. Instead we give Carol the observational BDD that checks whether
$P_{2k} \lor P_{2k + 1}$ has the same value in both worlds, i.e. the BDD of
$(P_{2k}' \lor P_{2k + 1}') \leftrightarrow (P_{2k}' \lor P_{2k + 1}')$.

To make it general, most functions are parameterized by n, the total number
of cards.

\begin{code}
rcPlayers :: [Agent]
rcPlayers = [alice,bob,carol]

rcNumOf :: Agent -> Int
rcNumOf i = fromMaybe (error "Unknown Agent") (elemIndex i rcPlayers)

nCards :: Int -> [Int]
nCards n = [0..(n-1)]

rcProps :: Int -> [Prp]
rcProps n = [ P k | k <-[0..((2*n)-1)] ]

hasCard :: Agent -> Int -> Form
hasCard "Alice" k = PrpF (P (2 * k))
hasCard "Bob"   k = PrpF (P ((2 * k) + 1))
hasCard "Carol" k = Neg $ Disj [hasCard "Alice" k, hasCard "Bob" k]
hasCard _       _ = error "Unknown Agent"

noDoubles :: Int -> Form
noDoubles n = Conj [ notDOuble k | k <- nCards n ] where
  notDOuble k = Neg $ Conj [alice `hasCard` k, bob `hasCard` k]

type RusCardProblem = (Int,Int,Int)

distribute :: RusCardProblem -> Form
distribute (na,nb,nc) = Conj [ alice `hasAtLeast` na, bob `hasAtLeast` nb ] where
  n = na + nb + nc
  hasAtLeast :: Agent -> Int -> Form
  hasAtLeast _ 0 = Top
  hasAtLeast i 1 = Disj [ i `hasCard` k | k <- nCards n ]
  hasAtLeast i 2 = Disj [ Conj (map (i `hasCard`) [x, y]) | x <- nCards n, y <- nCards n, x/=y ]
  hasAtLeast i 3 = Disj [ Conj (map (i `hasCard`) [x, y, z]) | x<-nCards n, y<-nCards n, z<-nCards n, x/=y, x/=z, y/=z ]
  hasAtLeast i k = Disj [ Conj (map (i `hasCard`) set) | set <- sets ] where
    sets = filter alldiff $ nub $ map sort $ replicateM k (nCards n) where
      alldiff [] = True
      alldiff (x:xs) = x `notElem` xs && alldiff xs

dontChange :: [Form] -> Bdd
dontChange fs = conSet [ mvBdd b `equ` cpBdd b | b <- map boolBddOf fs ]

rusSCNfor :: RusCardProblem -> GenScenario
rusSCNfor (na,nb,nc) = (GenKnS props law (fromList [ (i, obsbdd i) | i <- rcPlayers ]), defaultDeal) where
  n = na + nb + nc
  props   = [ P k | k <-[0..((2 * n)-1)] ]
  law = boolBddOf $ Conj [ noDoubles n, distribute (na,nb,nc)  ]
  obsbdd "Alice" = dontChange [ PrpF (P $ 2*k) | k <- [0..(n-1)] ]
  obsbdd "Bob"   = dontChange [ PrpF (P $ (2*k) + 1) | k <- [0..(n-1)] ]
  obsbdd "Carol" = dontChange [ Disj [PrpF (P $ 2*k), PrpF (P $ (2*k) + 1)] | k <- [0..(n-1)] ]
  obsbdd _       = error "Unkown Agent"
  defaultDeal =  [ let (PrpF p) = i `hasCard` k in p | i <- [alice,bob], k <- cardsFor i ] where
    cardsFor "Alice" = [0..(na-1)]
    cardsFor "Bob"   = [na..(na+nb-1)]
    cardsFor "Carol" = [(na+nb)..(na+nb+nc-1)]
    cardsFor _       = error "Unkown Agent"
\end{code}

\begin{code}
aAnnounce :: Form
aAnnounce = K alice $ Disj [ Conj (map (alice `hasCard`) hand) |
  hand <- [ [0,1,2], [0,3,4], [0,5,6], [1,3,5], [2,4,6] ] ]

bAnnounce :: Form
bAnnounce = K bob (carol `hasCard` 6)
\end{code}

To describe the goals of the protocol we need formulas about the knowledge of the three agents:
  Alice should know Bob's cards,
  Bob should know Alice's cards, and
  Carol should be ignorant, i.e. not know for any card that Alice or Bob has it.
  Note that Carol will still know for one card that neither Alice and Bob have them, namely his own. This is why we use $K^?$ (which is \texttt{Kw} in Haskell) for the first two but only the plain $K$ for the last condition.

\begin{code}
aKnowsBs, bKnowsAs, cIgnorant :: Int -> Form
aKnowsBs  n = Conj [ alice `Kw` (bob `hasCard` k) | k <- nCards n ]
bKnowsAs  n = Conj [ bob `Kw` (alice `hasCard` k) | k <- nCards n ]
cIgnorant n = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i <- nCards n ]
\end{code}

\textbf{CONCRETE EXAMPLE}

We can now check how the knowledge of the agents changes during the communication, i.e.~after the first and the second announcement.
First we check that Alice says the truth.

We replace the CK checks with "everyone knows" because Ck is not yet implemented
in the NonS5 module.

\begin{code}
myn :: Int
myn = 7

ek :: [Agent] -> Form -> Form
ek is f = Conj [ K i f | i <- is ]

rcCheck :: Int -> Form
rcCheck 0 = aAnnounce
\end{code}

After Alice announces five hands, Bob knows Alice's card and this is common knowledge among them.
\begin{code}
rcCheck 1 = PubAnnounce aAnnounce (bKnowsAs myn)
rcCheck 2 = PubAnnounce aAnnounce (ek [alice,bob] (bKnowsAs myn))
\end{code}

And Bob knows Carol's card. This is entailed by the fact that Bob knows Alice's cards.
\begin{code}
rcCheck 3 = PubAnnounce aAnnounce (K bob (carol `hasCard` 6))
\end{code}

Carol remains ignorant of Alice's and Bob's cards, and this is common knowledge.
\begin{code}
rcCheck 4 = PubAnnounce aAnnounce (ek [alice,bob,carol] (cIgnorant myn))
\end{code}

After Bob announces Carol's card, it is common knowledge among Alice and Bob that they know each others cards and Carol remains ignorant.
\begin{code}
rcCheck 5 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (ek [alice,bob] (aKnowsBs myn)))
rcCheck 6 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (ek [alice,bob] (bKnowsAs myn)))
rcCheck _ = PubAnnounce aAnnounce (PubAnnounce bAnnounce (ek rcPlayers (cIgnorant myn)))

rcAllChecks :: Bool
rcAllChecks = evalViaBdd (rusSCNfor (3,3,1)) (Conj (map rcCheck [0..7]))
\end{code}

Verifying this protocol for the fixed deal $012|345|6$ with our symbolic model checker takes about one second.
Moreover, checking multiple protocols in a row does not take much longer because the BDD package caches results.
Compared to that, the DEMO implementation from \cite{Ditmarsch06:MCRC} needs 4 seconds to check one protocol.

Run: SMCDEL.Examples.rcAllChecks % TODO

We can not just verify but also \emph{find} all protocols based on a set of five, six or seven hands, using the following combination of manual reasoning and brute-force.
The following function \texttt{checkSet} takes a set of cards and returns whether it can safely be used by Alice.

\begin{code}
checkSet :: [[Int]] -> Bool
checkSet set = all (evalViaBdd (rusSCNfor (3,3,1))) fs where
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` 6)
  fs = [ aliceSays
       , PubAnnounce aliceSays (bKnowsAs myn)
       , PubAnnounce aliceSays (Ck [alice,bob] (bKnowsAs myn))
       , PubAnnounce aliceSays (Ck [alice,bob,carol] (cIgnorant myn))
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck [alice,bob] $ Conj [aKnowsBs myn, bKnowsAs myn]))
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck rcPlayers (cIgnorant myn))) ]

possibleHands :: [[Int]]
possibleHands = [ [x,y,z] | x <- nCards myn, y <- nCards myn, z <- nCards myn, x < y, y < z ]

pickHands :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHands _ 0 = [ [ [ ] ] ]
pickHands unused 1 = [ [h] | h <- unused ]
pickHands unused n = concat [ [ h:hs | hs <- pickHands (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> length (h `intersect` xs) < 2 && h < xs)
\end{code}

The last line includes two important restrictions to the set of possible lists of hands that we will consider.
  First, Proposition 32 in \cite{vDitm2003:RC} tells us that safe announcements from Alice never contain ``crossing'' hands, i.e. two hands which have more than one card in common.
  Second, without loss of generality we can assume that the hands in her announcement are lexicographically ordered.
  This leaves us with 1290 possible lists of five, six or seven hands of three cards.

\begin{code}
allHandLists :: [ [ [Int] ] ]
allHandLists = concatMap (pickHands possibleHands) [5,6,7]
\end{code}

\myHaskellResult{length allHandLists}{rusAllHandListsLength}

Which of these are actually safe announcements that can be used by Alice?
We can find them by checking 1290 instances of \texttt{checkSet} above.
Our model checker can filter out the 102 safe announcements within seconds, generating and verifying the same list as in \cite[Figure 3]{vDitm2003:RC} where it was manually generated.

\begin{showCode}
*EXAMPLES> mapM_ print (sort (filter checkSet allHandLists))
[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6]]
[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]]
[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,4,5]]
[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[2,3,6],[2,4,5]]
...
[[0,1,2],[0,5,6],[1,3,6],[1,4,5],[2,3,5],[2,4,6]]
[[0,1,2],[0,5,6],[1,3,6],[2,4,6],[3,4,5]]
[[0,1,2],[0,5,6],[1,4,5],[2,3,5],[3,4,6]]
[[0,1,2],[0,5,6],[1,4,6],[2,3,6],[3,4,5]]
(3.39 secs, 825215584 bytes)
\end{showCode}

\myHaskellResult{length (filter checkSet allHandLists)}{rusExchangeLengths}


\paragraph{Protocol synthesis}.
We now adopt an even more general perspective which is considered in \cite{engetal2015:cooplan}.
Fix that Alice has $\{0,1,2\}$ and that she will announce 5 hands, including this one.
Hence she has to pick 4 other hands of three cards each, i.e.~she has to choose among 46376 possible actions.

\begin{code}
pickHandsNaive :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHandsNaive _ 0 = [ [ [ ] ] ]
pickHandsNaive unused 1 = [ [h] | h <- unused ]
pickHandsNaive unused n = concat [ [ h:hs | hs <- pickHandsNaive (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> h < xs)

alicesActions :: [[[Int]]]
alicesActions = pickHandsNaive (delete [0,1,2] possibleHands) 4
\end{code}

\myHaskellResult{choose ((choose 7 3)-1) 4 == length alicesActions}{numOfAlicesActions}

\begin{code}
alicesForms :: [Form]
alicesForms = map translate alicesActions

translate :: [[Int]] -> Form
translate set = Disj [ Conj $ map (alice `hasCard`) h | h <- [0,1,2]:set ]

bobsForms :: [Form]
bobsForms = [carol `hasCard` n | n <- reverse [0..6]] -- FIXME relax!

allPlans :: [(Form,Form)]
allPlans = [ (a,b) | a <- alicesForms, b <- bobsForms ]
\end{code}

For example: $\myHaskTexN{head alicesForms}{headAlicesForms}$

\begin{code}
testPlan :: (Form,Form) -> Bool
testPlan (aSays,bSays) = all (evalViaBdd (rusSCNfor (3,3,1))) fs where
  fs = [ aSays
       , PubAnnounce aSays (bKnowsAs myn)
       , PubAnnounce aSays (Ck [alice,bob] (bKnowsAs myn))
       , PubAnnounce aSays (Ck [alice,bob,carol] (cIgnorant myn))
       , PubAnnounce aSays bSays
       , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob] $ Conj [aKnowsBs myn, bKnowsAs myn]))
       , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob,carol] (cIgnorant myn))) ]

rcSolutions :: [(Form, Form)]
rcSolutions = filter testPlan allPlans
\end{code}

% TODO: rerun this now, hopefully fasterrrrr?!
It now takes 160.89 seconds to generate all the working plans when we fix \texttt{bobsForms = hasCard carol 6}.
Given the definition above it takes 1125.06 seconds.
In both cases we find the same 60 solutions.


For the following cases it is unknown whether a multi-announcement solution exists.
(It \emph{is} known that no two-announcement solution exists.)
\begin{itemize}
  \item (2,2,1)
  \item (3,2,1)
  \item (3,3,2)
\end{itemize}

We model a deterministic \emph{plan} as a list of pairs of formulas. The first
part of the first tuple should be announced truthfully and lead to a model
where the second part of the tuple is true. Then we continue with the next
tuple.
% TODO: spell out a formal definition with a Sequence -> Formula translation.

\begin{code}
type Plan = [(Form,Form)] -- list of (announcement,goal) tuples

succeeds :: Plan -> Form
succeeds [] = Top
succeeds ((step,goal):rest) =
  Conj [step, PubAnnounce step goal, PubAnnounce step (succeeds rest)]

succeedsOn :: Plan -> GenScenario -> Bool
succeedsOn plan scn = evalViaBdd scn (succeeds plan)

-- the plan for (3,3,1)
basicPlan :: Plan
basicPlan =
  [ (aAnnounce, Conj [ bKnowsAs myn, Ck [alice,bob] (bKnowsAs myn), Ck [alice,bob,carol] (cIgnorant myn) ] )
  , (bAnnounce, Conj [ aKnowsBs myn, Ck [alice,bob] (aKnowsBs myn), Ck rcPlayers (cIgnorant myn) ] ) ]

possibleHandsN :: Int -> Int -> [[Int]]
possibleHandsN n na = filter alldiff $ nub $ map sort $ replicateM na (nCards n) where
  alldiff [] = True
  alldiff (x:xs) = x `notElem` xs && alldiff xs

allHandListsN :: Int -> Int -> [ [ [Int] ] ]
allHandListsN n na = concatMap (pickHands (possibleHandsN n na)) [5,6,7] -- FIXME how to adapt the number of hands for larger n?
\end{code}

Note that we still use the same pickHands.
% TODO
This is a problem because of the intersection constraint!
The only should have striclty less than (na - nc) cards in common!

\begin{code}
aKnowsBsN, bKnowsAsN, cIgnorantN :: Int -> Form
aKnowsBsN n = Conj [ alice `Kw` (bob `hasCard` k) | k <- nCards n ]
bKnowsAsN n = Conj [ bob `Kw` (alice `hasCard` k) | k <- nCards n ]
cIgnorantN n = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i <- nCards n ]

checkSetFor :: RusCardProblem -> [[Int]] -> Bool
checkSetFor (na,nb,nc) set = plan `succeedsOn` rusSCNfor (na,nb,nc) where
  n = na + nb + nc
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` last (nCards n))
  plan =
   [ (aliceSays, Conj [ bKnowsAsN n, Ck [alice,bob] (bKnowsAsN n), Ck [alice,bob,carol] (cIgnorantN n) ] )
   , (bobSays  , Conj [ Ck [alice,bob] $ Conj [aKnowsBsN n, bKnowsAsN n], Ck rcPlayers (cIgnorantN n) ] )
   ]

checkHandsFor :: RusCardProblem -> [ ( [[Int]], Bool) ]
checkHandsFor (na,nb,nc) = map (\hs -> (hs, checkSetFor (na,nb,nc) hs)) (allHandListsN n na) where
  n = na + nb + nc

allCasesUpTo :: Int -> [RusCardProblem]
allCasesUpTo bound = [ (na,nb,nc) | na <- [1..bound]
                                  , nb <- [1..(bound-na)]
                                  , nc <- [1..(bound-(na+nb))]
                                  -- these restrictions are only proven
                                  -- for two announcement plans ...
                                  , nc < (na - 1)
                                  , nc < nb ]
\end{code}

% TODO: go on
Now we should think about protocols with more than two steps!


\begin{code}
main :: IO ()
main = do
  print $ rusSCNfor (3,3,1)
  mapM_ print (sort (filter checkSet allHandLists))
\end{code}
