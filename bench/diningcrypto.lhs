
\subsection{Dining Cryptographers}

\label{BENCHDC}

Muddy Children has also been used to benchmark MCMAS \cite{mcmas} but the formula checked there concerns the correctness of behavior and not how many rounds are needed.
Moreover, the interpreted system semantics of model checkers like MCMAS are very different from DEL. Still, connections between DEL and temporal logics have been studied and translations are available \cite{vB2009merging,ditmarsch2013connecting}.

A protocol which fits nicely into both frameworks are the Dining Cryptographers \cite{DiningCrypto} which we implemented in Section \ref{subsec-diningcryptos}.
We will now use it to measure the performance of \emph{SMCDEL} in a way that is more similar to \cite{mcmas}.

\begin{code}
module Main (main) where
import Control.Monad (when)
import Data.Time (diffUTCTime,getCurrentTime,NominalDiffTime)
import System.Environment (getArgs)
import System.IO (hSetBuffering,BufferMode(NoBuffering),stdout)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD
import SMCDEL.Examples (genDcKnsInit,genDcReveal)
\end{code}

The following statement was also checked with MCMAS in \cite{mcmas}.
\begin{quote}
``If cryptographer 1 did not pay the bill, then after the announcements are made, he knows that no cryptographers paid, or that someone paid, but in this case he does not know who did.''
\end{quote}
Following ideas and conventions from \cite{vB2009merging,ditmarsch2013connecting} we can formalize it in DEL as
\[ \lnot p_1
  \rightarrow
  [! \psi]
  \left(
    K_1 ( \bigwedge_{i=1}^n \lnot p_i )
  \lor
    \left(
      K_1 ( \bigvee_{i=2}^n p_i )
      \land
      \bigwedge_{i=2}^n ( \lnot K_1 p_i )
    \right)
  \right) \]
where $p_i$ says that agent $i$ paid and $!\psi$ is the announcement whether the number of agents which announced a $1$ is odd, i.e. $\psi := \bigoplus_i \bigoplus \{ p \mid \text{Agent $i$ can observe $p$} \} $.

\begin{code}
genDcCheckForm :: Int -> Form
genDcCheckForm n = Impl (Neg (PrpF $ P 1)) $
  PubAnnounceW (Xor [genDcReveal n i | i<-[1..n] ]) $
    Disj [ K "1" (Conj [Neg $ PrpF $ P k | k <- [1..n]  ])
         , Conj [ K "1" (Disj [ PrpF $ P k | k <- [2..n] ])
                , Conj [ Neg $ K "1" (PrpF $ P k) | k <- [2..n] ] ] ]
\end{code}

\begin{code}
genDcValid :: Int -> Bool
genDcValid n = validViaBdd (genDcKnsInit n) (genDcCheckForm n)

dcTimeThis :: Int -> IO NominalDiffTime
dcTimeThis n = do
  start <- getCurrentTime
  let mykns@(KnS props _ _) = genDcKnsInit n
  putStr $ show (length props) ++ "\t"
  putStr $ show (length $ show mykns) ++ "\t"
  putStr $ show (length $ show $ genDcCheckForm n) ++ "\t"
  if genDcValid n then do
    end <- getCurrentTime
    return (end `diffUTCTime` start)
  else
    error "Wrong result."

mainLoop :: [Int] -> Int -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n:ns) limit = do
  putStr $ show n ++ "\t"
  result <- dcTimeThis n
  print result
  when (result <= fromIntegral limit) $ mainLoop ns limit

main :: IO ()
main = do
  args <- getArgs
  hSetBuffering stdout NoBuffering
  limit <- case args of
    [aInteger] | [(n,_)] <- reads aInteger -> return n
    _ -> do
      putStrLn "No maximum runtime given, defaulting to one second."
      return 1
  putStrLn $ "n" ++ "\tn(prps)"++ "\tsz(KNS)"++ "\tsz(frm)" ++ "\ttime"
  mainLoop (3:(5 : map (10*) [1..])) limit
\end{code}

The program outputs the following table which shows
(i) the number of cryptographers,
(ii) the number of propositions used,
(iii) the length of the knowledge structure,
(iv) the length of the formula and
(v) the time in seconds needed by SMCDEL to check it.

% \lstinputlisting{benchdc.dat}

These results are satisfactory: While MCMAS already needs more than 10 seconds to check the interpreted system for 50 or more dining cryptographers (see \cite[Table 4]{mcmas}), \emph{SMCDEL} can deal with the case of up to 160 agents in less time.
