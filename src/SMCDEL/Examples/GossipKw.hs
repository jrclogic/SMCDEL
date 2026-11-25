{-# LANGUAGE TemplateHaskell #-}

{- |

__Knowing-whether Gossip on belief structures with epistemic change__

We consider the classic telephone problem where \(n\) agents each know only their
own secret in the beginning and then make phone calls in which they always
exchange all secrets they know.
For now we only consider static and not dynamic gossip, i.e.\ all agents can
call all others --- the \(N\) relation is total.

In this section we follow the following article and use /knowing-whether/:
Agent \(a\) knows the secret of \(b\) iff \(K_a^? p_b\).


- [ADGH2014]
  Maduka Attamah, Hans van Ditmarsch, Davide Grossi and Wiebe van der Hoek (2014):
  /Knowledge and Gossip/.
  23rd ECAI.
  <https://doi.org/10.3233/978-1-61499-419-0-21>

We use belief instead of knowledge structures because this makes it much
easier to describe the event observation law.
Otherwise we would have to add a lot more observational variables.

Still, the relations actually will be equivalences — despite the name, nobody
is being deceived in the classic gossip problem as we model it here. Hence not
using knowledge structures optimized for S5 is a big waste.

In "SMCDEL.Examples.GossipS5" we present an alternative model which is an
abstraction of the one here and performs better, but has other limitations.
-}

module SMCDEL.Examples.GossipKw where

import SMCDEL.Language
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Symbolic.K
import SMCDEL.Internal.TexDisplay

import Control.Arrow ((&&&))
import Data.HasCacBDD hiding (Top)
import Data.Map.Strict (Map,fromList,empty)
import Data.List ((\\),sort)

-- | We fix the number of agents at \(4\ for now.
n :: Int
n = 4

-- | The initial structure for the gossip problem.
gossipInit :: BelScene
gossipInit = (BlS vocab law obs, actual) where
  vocab  = map P [1..n]
  law    = boolBddOf Top
  obs    = fromList [ (show i, allsamebdd [P i]) | i <- [1..n] ]
  actual = vocab
$(addSvg 'gossipInit)

-- | Formula to say whether in the given call the given secret will be exchanged.
willExchangeT :: (Int,Int) -> Int -> Form
willExchangeT (a,b) k | k `elem` [a,b] = PrpF (P k)
                      | otherwise      = Disj [ K (show i) $ PrpF (P k) | i <- [a,b] ]

inCall,inSecT :: Int -> Prp
inCall k = P (100+k) -- k participates in the call
inSecT k = P (200+(k*2)) -- secret k is being exchanged (as true)

call :: (Int,Int) -> [Int] -> Event
call (a,b) secSetT = (callTrf,actualSet) where
  actualSet = [inCall a, inCall b] ++ map inSecT secSetT

-- | Knowledge Transformer to make a call.
callTrf :: Transformer
callTrf = Trf vocplus lawplus empty obsplus where
  vocplus = sort $ map inCall [1..n] ++ map inSecT [1..n]
  lawplus = simplify $ Disj [ Conj [ thisCallHappens i j, theseSecretsAreExchanged i j ]  | i <- [1..n], j <- [1..n], i < j ] where
    thisCallHappens i j = Conj $ map (PrpF . inCall) [i,j] ++ map (Neg . PrpF . inCall) ([1..n] \\ [i,j])
    -- lnsPreCondition i j = Neg $ K (show i) (PrpF $ P j)
    theseSecretsAreExchanged i j = simplify $ Conj
      [ PrpF (inSecT k) `Equi` willExchangeT (i,j) k | k <- [1..n] ]
  obsplus :: Map Agent RelBDD
  obsplus = fromList $ map (show &&& obsfor) [1..n] where
    obsfor i = con <$> allsamebdd [ inCall i ]
                   <*> (imp <$> (mvBdd . boolBddOf . PrpF $ inCall i)
                            <*> allsamebdd (sort $ map inCall [1..n] ++ map inSecT [1..n]))
$(addSvg 'gossipInit)

{- $

The following is an ad-hoc solution to calculate `secSetT` in advance.
A more efficient implementation should use multi-pointed transformers.

-}

toBeExchangedT :: BelScene -> (Int,Int) -> [Int]
toBeExchangedT scn (a,b) = filter (evalViaBdd scn . willExchangeT (a,b)) [1..n]

doCall :: BelScene -> (Int,Int) -> BelScene
doCall start (a,b) = cleanupObsLaw $ start `update` call (a,b) (toBeExchangedT start (a,b))

doCalls :: BelScene -> [(Int,Int)] -> BelScene
doCalls = foldl doCall

expert :: Int -> Form
expert k = Conj [ K (show k) $ PrpF (P i) | i <- [1..n] ]

allExperts :: Form
allExperts = Conj $ map expert [1..n]

whoKnowsWhat :: BelScene -> [(Int,[Int])]
whoKnowsWhat scn = [ (k, filter (knownBy k) [1..n]) | k <- [1..n] ] where
  knownBy k i = evalViaBdd scn (K (show k) $ PrpF (P i))

-- What do agents know, and what do they know about each others knowledge?
whoKnowsMeta :: BelScene -> [(Int,[(Int,String)])]
whoKnowsMeta scn = [ (k, map (meta k) [1..n] ) | k <- [1..n] ] where
  meta x y = (y, map (knowsAbout x y) [1..n])
  knowsAbout x y i
    | evalViaBdd scn (K (show x) $ PrpF (P i) `Impl` K (show y) (PrpF (P i))) = 'Y'
    | evalViaBdd scn (Neg $ K (show x) $ Neg $ K (show y) $ PrpF (P i))       = '?'
    | evalViaBdd scn (K (show x) $ Neg $ K (show y) $ PrpF (P i))             = '_'
    | otherwise                                                               = 'E'

after :: [(Int,Int)] -> BelScene
after = doCalls gossipInit

succeeds :: [(Int,Int)] -> Bool
succeeds sequ = evalViaBdd (after sequ) allExperts

allSequs :: Int -> [ [(Int,Int)] ]
allSequs 0 = [ [] ]
allSequs l = [ (i,j):rest | rest <- allSequs (l-1), i <- [1..n], j <- [1..n], i < j ]

{- $

For example, the following is not a success sequence for four agents:

>>> SMCDEL.Examples.GossipKw.succeeds [(1,2),(2,3),(3,1)]
False

But this is:

>>> SMCDEL.Examples.GossipKw.succeeds [(1,2),(3,4),(1,3),(2,4)]
True

-}
