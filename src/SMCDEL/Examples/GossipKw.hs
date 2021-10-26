module SMCDEL.Examples.GossipKw where

import SMCDEL.Language
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Symbolic.K

import Control.Arrow ((&&&))
import Data.HasCacBDD hiding (Top)
import Data.Map.Strict (Map,fromList,empty)
import Data.List ((\\),sort)

n :: Int
n = 4

gossipInit :: BelScene
gossipInit = (BlS vocab law obs, actual) where
  vocab  = map P [1..n]
  law    = boolBddOf Top
  obs    = fromList [ (show i, allsamebdd [P i]) | i <- [1..n] ]
  actual = vocab

willExchangeT :: (Int,Int) -> Int -> Form
willExchangeT (a,b) k | k `elem` [a,b] = PrpF (P k)
                      | otherwise      = Disj [ K (show i) $ PrpF (P k) | i <- [a,b] ]

inCall,inSecT :: Int -> Prp
inCall k = P (100+k) -- k participates in the call
inSecT k = P (200+(k*2)) -- secret k is being exchanged (as true)

call :: (Int,Int) -> [Int] -> Event
call (a,b) secSetT = (callTrf,actualSet) where
  actualSet = [inCall a, inCall b] ++ map inSecT secSetT

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
