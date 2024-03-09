{- |

This benchmark uses "SMCDEL.Examples.DiningCrypto".
We use it to compare the performance of SMCDEL with the temporal epistemic logic
model checker [MCMAS](https://vas.doc.ic.ac.uk/software/mcmas/) from

- "Alessio Lomuscio, Hongyang Qu, Franco Raimondi (2015):
  /MCMAS: an open-source model checker for the verification of multi-agent systems/.
  <https://doi.org/10.1007/s10009-015-0378-x>

There the following statement was checked:
"If cryptographer 1 did not pay the bill, then after the announcements are
made, he knows that no cryptographers paid, or that someone paid, but in
this case he does not know who did."

Wwe formalize the same statement in DEL as:
\[
  \lnot p_1
  \rightarrow
  [!? \psi]
  \left(
    K_1 ( \bigwedge_{i=1}^n \lnot p_i )
  \lor
    \left(
      K_1 ( \bigvee_{i=2}^n p_i )
      \land
      \bigwedge_{i=2}^n ( \lnot K_1 p_i )
    \right)
  \right)
\]
where \(p_i\) says that agent \(i\) paid and \(!? \psi\) is the public announcement
whether the number of agents which announced a \(1\) is odd or even, i.e.
\(\psi := \bigoplus_i \bigoplus \{ p \mid \text{Agent $i$ can observe $p$} \}\).

To run this benchmark, run @stack bench smcdel:bench:bench-diningcrypto@ in the SMCDEL folder.

The program outputs a table like the following, showing in five columns
(i) the number of cryptographers,
(ii) the number of propositions used,
(iii) the length of the knowledge structure,
(iv) the length of the formula and
(v) the time in seconds needed by SMCDEL to check it.

> n       n(prps) sz(KNS) sz(frm) time
> 3       7       217     339     0.1372
> 4       11      332     477     0.0005
> 5       16      483     645     0.0008
> 10      56      1654    1847    0.0023
> 20      211     6497    6289    0.0091
> 30      466     14572   13419   0.0283
> 40      821     25747   23149   0.0619
> 50      1276    40850   36031   0.1212
> 60      1831    59890   52071   0.2229
> 70      2486    82330   70911   0.4160
> 80      3241    108170  92551   0.7038
> 90      4096    137410  116991  1.0987

MCMAS needs more than 10 seconds to check the interpreted system for 50 or
more dining cryptographers (see Lomuscio et al., Table 4), but SMCDEL can
deal with the DEL model of up to 160 agents in less time.
Note however, that the DEL model we use is less detailed than the temporal
model. In particular, we take synchronous perfect recall for granted and
merge all broadcasts done by different agents into one public announcement.

Note that the result for three agents is slower just because we compute it
first. The same happens if we start at four or five agents. The reason is
that initializing the BDD package takes some time, but is done only once.

-}
module Main (main) where

import Control.Monad (when)
import Data.Time (diffUTCTime,getCurrentTime,NominalDiffTime)
import System.Environment (getArgs)
import System.IO (hSetBuffering,BufferMode(NoBuffering),stdout)
import Text.Printf

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Examples.DiningCrypto

-- | The formula to be checked.
-- Note that this formula is different from the one in "SMCDEL.Examples.DiningCrypto"
benchDcCheckForm :: Int -> Form
benchDcCheckForm n =
  PubAnnounceW (Xor [genDcReveal n i | i<-[1..n] ]) $
  -- pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $ -- slow!
    Impl (Neg (PrpF $ P 1)) $
      Disj [ K "1" (Conj [Neg $ PrpF $ P k | k <- [1..n]  ])
           , Conj [ K "1" (Disj [ PrpF $ P k | k <- [2..n] ])
                  , Conj [ Neg $ K "1" (PrpF $ P k) | k <- [2..n] ] ] ]

benchDcValid :: Int -> Bool
benchDcValid n = validViaBdd (genDcKnsInit n) (benchDcCheckForm n)

dcTimeThis :: Int -> IO NominalDiffTime
dcTimeThis n = do
  start <- getCurrentTime
  let mykns@(KnS props _ _) = genDcKnsInit n
  putStr $ show (length props) ++ "\t"
  putStr $ show (length $ show mykns) ++ "\t"
  putStr $ show (length $ show $ benchDcCheckForm n) ++ "\t"
  if benchDcValid n then do
    end <- getCurrentTime
    return (end `diffUTCTime` start)
  else
    error "Wrong result."

mainLoop :: [Int] -> Int -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n:ns) limit = do
  putStr $ show n ++ "\t"
  result <- dcTimeThis n
  printf "%.4f\n" (realToFrac result :: Double)
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
  mainLoop (3:4:(5 : map (10*) [1..])) limit
