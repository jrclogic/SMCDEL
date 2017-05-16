
We now provide two different benchmarks for SMCDEL.
All measurements were done under
  64-bit Debian GNU/Linux 8
  with kernel 3.16.0-4 running
  on an Intel Core i3-2120 3.30GHz processor
  and 4GB of memory.
Code was compiled with GHC 7.10.3 and g++ 4.9.2.

\subsection{Muddy Children}

\label{BENCHMC}

In this section we compare the performance of different model
checking approaches to the muddy children example from Section
\ref{subsec:muddychildren}.

\begin{itemize}
  \item SMCDEL with two different BDD packages: CacBDD and CUDD.
  \item DEMO-S5, a version of the epistemic model checker DEMO optimized for S5 \cite{JvE:DEMO,JvE:DEMOS5}.
  \item MCTRIANGLE, an ad-hoc implementation of \cite{Gierasimczuk2011:genmc}, see Appendix 1 on page \pageref{appendix-triangle}.
\end{itemize}

Note that to run this program all libraries, in particular the BDD
packages have to be installed and get found by the dynamic linker.

\begin{code}
module Main where
import Criterion.Main
import Data.Function
import Data.List
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import SMCDEL.Language
import SMCDEL.Examples
import SMCDEL.Internal.Help (apply,seteq)
import qualified SMCDEL.Explicit.DEMO_S5 as DEMO_S5
import qualified SMCDEL.Explicit.Simple
import qualified SMCDEL.Symbolic.HasCacBDD
import qualified SMCDEL.Symbolic.CUDD
import qualified SMCDEL.Translations
import qualified SMCDEL.Other.MCTRIANGLE
import qualified SMCDEL.Other.NonS5
import Data.Map.Strict (fromList)
\end{code}

This benchmark compares how long it takes to answer the following question:
"For $n$ children, when $m$ of them are muddy, how many announcements of >>Nobody knows their own state.<< are needed to let at least one child know their own state?".
For this purpose we recursively define the formula to be checked and a general loop function which uses a given model checker to find the answer.

\begin{code}
checkForm :: Int -> Int -> Form
checkForm n 0 = nobodyknows n
checkForm n k = PubAnnounce (nobodyknows n) (checkForm n (k-1))

findNumberWith :: (Int -> Int -> a, a -> Form -> Bool) -> Int -> Int -> Int
findNumberWith (start,evalfunction) n m = k where
  k | loop 0 == (m-1) = m-1
    | otherwise       = error $ "wrong Muddy Children result: " ++ show (loop 0)
  loop count = if evalfunction (start n m) (PubAnnounce (father n) (checkForm n count))
    then loop (count+1)
    else count

mudPs :: Int -> [Prp]
mudPs n = [P 1 .. P n]
\end{code}

We now instantiate this function with the \texttt{evalViaBdd} function from our four different versions of SMCDEL, linked to the different BDD packages.

\begin{code}
findNumberCacBDD :: Int -> Int -> Int
findNumberCacBDD = findNumberWith (cacMudScnInit,SMCDEL.Symbolic.HasCacBDD.evalViaBdd) where
  cacMudScnInit n m = ( SMCDEL.Symbolic.HasCacBDD.KnS (mudPs n) (SMCDEL.Symbolic.HasCacBDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberCUDD :: Int -> Int -> Int
findNumberCUDD = findNumberWith (cuddMudScnInit,SMCDEL.Symbolic.CUDD.evalViaBdd) where
  cuddMudScnInit n m = ( SMCDEL.Symbolic.CUDD.KnS (mudPs n) (SMCDEL.Symbolic.CUDD.boolBddOf Top) [ (show i,delete (P i) (mudPs n)) | i <- [1..n] ], mudPs m )

findNumberTrans :: Int -> Int -> Int
findNumberTrans = findNumberWith (start,SMCDEL.Symbolic.HasCacBDD.evalViaBdd) where
  start n m = SMCDEL.Translations.kripkeToKns $ mudKrpInit n m

mudKrpInit :: Int -> Int -> SMCDEL.Explicit.Simple.PointedModel
mudKrpInit n m = (SMCDEL.Explicit.Simple.KrM ws rel val, cur) where
  ws    = [0..(2^n-1)]
  rel   = [ (show i, erelFor i) | i <- [1..n] ] where
    erelFor i = sort $ map sort $
      groupBy ((==) `on` setForAt i) $
      sortBy (comparing (setForAt i)) ws
    setForAt i s = delete (P i) $ setAt s
    setAt s = map fst $ filter snd (apply val s)
  val         = zip ws table
  ((cur,_):_) = filter (\(_,ass)-> sort (map fst $ filter snd ass) == [P 1..P m]) val
  table = foldl buildTable [[]] [P k | k<- [1..n]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

findNumberNonS5 :: Int -> Int -> Int
findNumberNonS5 = findNumberWith
  (SMCDEL.Other.NonS5.mudGenScnInit,SMCDEL.Other.NonS5.evalViaBdd)

findNumberNonS5Trans :: Int -> Int -> Int
findNumberNonS5Trans = findNumberWith (start,SMCDEL.Other.NonS5.evalViaBdd) where
  start n m = SMCDEL.Other.NonS5.genKrp2Kns $ mudGenKrpInit n m

mudGenKrpInit :: Int -> Int -> SMCDEL.Other.NonS5.GeneralPointedModel
mudGenKrpInit n m = (SMCDEL.Other.NonS5.GKM $ fromList wlist, cur) where
  wlist = [ (w, (fromList (vals !! w), fromList $ relFor w)) | w <- ws ]
  ws    = [0..(2^n-1)]
  vals  = map sort (foldl buildTable [[]] [P k | k<- [1..n]])
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor w = [ (show i, seesFrom i w) | i <- [1..n] ]
  seesFrom i w = filter (\v -> samefor i (vals !! w) (vals !! v)) ws
  samefor i ps qs = seteq (delete (P i) (map fst $ filter snd ps)) (delete (P i) (map fst $ filter snd qs))
  cur = fromJust (elemIndex curVal vals)
  curVal = sort $ [(p,True) | p <- [P 1 .. P m]] ++ [(p,True) | p <- [P (m+1) .. P n]]
\end{code}

However, for an explicit state model checker like DEMO-S5 we can not use the same loop function because we want to hand on the current model to the next step instead of computing it again and again.

\begin{code}
mudDemoKrpInit :: Int -> Int -> DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = DEMO_S5.Mo states agents [] rels points where
  states = DEMO_S5.bTables n
  agents = map DEMO_S5.Ag [1..n]
  rels = [(DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- DEMO_S5.bTables (i-1),
                   tab2 <- DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemoS5 :: Int -> Int -> Int
findNumberDemoS5 n m = findNumberDemoLoop n m 0 start where
  start = DEMO_S5.updPa (mudDemoKrpInit n m) (DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if DEMO_S5.isTrue curMod (DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (DEMO_S5.updPa curMod (DEMO_S5.dont n))
    else count
\end{code}

Also the number triangle approach to the Muddy Children puzzle has to be treated separately.
See \cite{Gierasimczuk2011:genmc} and Appendix 1 on page \pageref{appendix-triangle} for the details.
Here the formula \texttt{nobodyknows} does not depend on the number of agents and therefore the loop function does not have to pass on any variables.

\begin{code}
findNumberTriangle :: Int -> Int -> Int
findNumberTriangle n m = findNumberTriangleLoop 0 start where
  start = SMCDEL.Other.MCTRIANGLE.update (SMCDEL.Other.MCTRIANGLE.mcModel (n-m,m)) (SMCDEL.Other.MCTRIANGLE.Qf SMCDEL.Other.MCTRIANGLE.some)

findNumberTriangleLoop :: Int -> SMCDEL.Other.MCTRIANGLE.McModel -> Int
findNumberTriangleLoop count curMod =
  if SMCDEL.Other.MCTRIANGLE.eval curMod SMCDEL.Other.MCTRIANGLE.nobodyknows
    then findNumberTriangleLoop (count+1) (SMCDEL.Other.MCTRIANGLE.update curMod SMCDEL.Other.MCTRIANGLE.nobodyknows)
    else count
\end{code}

The following function uses the library \emph{Criterion} to benchmark
all the solution methods we defined.

\begin{code}
main :: IO ()
main = defaultMain (map mybench
  [ ("Triangle"  , findNumberTriangle  , [7..40] )
  , ("CacBDD"    , findNumberCacBDD    , [3..40] )
  , ("CUDD"      , findNumberCUDD      , [3..40] )
  , ("NonS5"     , findNumberNonS5     , [3..12] )
  , ("DEMOS5"    , findNumberDemoS5    , [3..12] )
  , ("Trans"     , findNumberTrans     , [3..12] )
  , ("NonS5Trans", findNumberNonS5Trans, [3..11] ) ])
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf (\n -> f n n) k
\end{code}

% \lstinputlisting{benchmc.dat}

\begin{figure}
  \centering
  \begin{tikzpicture}
    \pgfplotstableread{benchmc.dat}
    \datatable
    \begin{axis}[ymode=log, unbounded coords=jump, width=0.8\linewidth, grid=major, legend pos=north east, ylabel=seconds, xlabel=no. of children (all muddy)]
      \addlegendentry{DEMO-S5};
        \addplot table[y=DEMOS5] from \datatable;
      \addlegendentry{Trans};
        \addplot table[y=Trans] from \datatable;
      \addlegendentry{SMCDEL (CacBDD)};
        \addplot table[y=CacBDD] from \datatable;
      \addlegendentry{SMCDEL (CUDD)};
        \addplot table[y=CUDD] from \datatable;
      \addlegendentry{NonS5};
        \addplot table[y=NonS5] from \datatable;
      \addlegendentry{NonS5Trans};
        \addplot table[y=NonS5Trans] from \datatable;
      \addlegendentry{Triangle \cite{Gierasimczuk2011:genmc}} ;
        \addplot table[y=Triangle] from \datatable;
    \end{axis}
  \end{tikzpicture}
  \caption{Benchmark Results on a logarithmic scale.}\label{fig-resultplot}
\end{figure}

As expected we can see in Figure \ref{fig-resultplot} that \emph{SMCDEL} is faster than the explicit model checker DEMO.
% TODO: The two BDD packages with elaborate memory management give us the best performance for \emph{SMCDEL}, with a slightly better performance of CacBDD compared to CUDD.
% TODO: It is important to note that this difference and the performance in general also depends on the binding libraries we use.
% TODO: Especially concerning memory management and garbage collection there should be room for improvement.

Finally, the number triangle approach from \cite{Gierasimczuk2011:genmc} is way faster than all others, especially for large numbers of agents.
This is not surprising, though: Both the model and the formula which are checked here are smaller and the semantics was specifically adapted to the muddy children example.
Concretely, the size of the model is linear in the number of agents and the length of the formula is constant.
It will be subject to future work if the idea underlying this approach -- the identification of agents in the same informational state -- can be generalized to other protocols or ideally the full DEL language.
