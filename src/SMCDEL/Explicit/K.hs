{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Explicit.K where

import Control.Arrow ((&&&))
import Data.GraphViz
import Data.List (nub,sort,(\\),delete,elemIndex)
import Data.Map.Strict (Map,fromList,elems,(!),mapMaybeWithKey)
import qualified Data.Map.Strict

import SMCDEL.Language
import SMCDEL.Explicit.S5 (World,HasWorlds,worldsOf,Action)
import SMCDEL.Internal.Help (alleqWith,lfp,seteq)
import SMCDEL.Internal.TexDisplay

newtype KripkeModel = KrM (Map World (Map Prp Bool, Map Agent [World]))
  deriving (Eq,Ord,Show)

type PointedModel = (KripkeModel, World)

distinctVal :: KripkeModel -> Bool
distinctVal (KrM m) = Data.Map.Strict.size m == length (nub (map fst (elems m)))

instance HasWorlds KripkeModel where
  worldsOf (KrM m) = Data.Map.Strict.keys m

instance HasVocab KripkeModel where
  vocabOf (KrM m) = Data.Map.Strict.keys $ fst (head (Data.Map.Strict.elems m))

instance HasAgents KripkeModel where
  agentsOf (KrM m) = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems m))

instance HasWorlds PointedModel where worldsOf = worldsOf . fst
instance HasVocab PointedModel  where vocabOf  = vocabOf  . fst
instance HasAgents PointedModel where agentsOf = agentsOf . fst

relOfIn :: Agent -> KripkeModel -> Map World [World]
relOfIn i (KrM m) = Data.Map.Strict.map (\x -> snd x ! i) m

truthsInAt :: KripkeModel -> World -> [Prp]
truthsInAt (KrM m) w = Data.Map.Strict.keys (Data.Map.Strict.filter id (fst (m ! w)))

instance KripkeLike KripkeModel where
  directed = const True
  getNodes m = map (show . fromEnum &&& labelOf) (worldsOf m) where
    labelOf w = "$" ++ tex (truthsInAt m w) ++ "$"
  getEdges m =
    concat [ [ (a, show $ fromEnum w, show $ fromEnum v) | v <- relOfIn a m ! w ] | w <- worldsOf m, a <- agentsOf m ]
  getActuals = const []

instance KripkeLike PointedModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals = return . show . fromEnum . snd

instance TexAble KripkeModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance TexAble PointedModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

exampleModel :: KripkeModel
exampleModel = KrM $ fromList
  [ (1, (fromList [(P 0,True ),(P 1,True )], fromList [(alice,[1]), (bob,[1])] ) )
  , (2, (fromList [(P 0,False),(P 1,True )], fromList [(alice,[1]), (bob,[2])] ) ) ]

examplePointedModel :: PointedModel
examplePointedModel = (exampleModel,1)

eval :: PointedModel -> Form -> Bool
eval _     Top           = True
eval _     Bot           = False
eval (m,w) (PrpF p)      = p `elem` truthsInAt m w
eval pm    (Neg f)       = not $ eval pm f
eval pm    (Conj fs)     = all (eval pm) fs
eval pm    (Disj fs)     = any (eval pm) fs
eval pm    (Xor  fs)     = odd $ length (filter id $ map (eval pm) fs)
eval pm    (Impl f g)    = not (eval pm f) || eval pm g
eval pm    (Equi f g)    = eval pm f == eval pm g
eval pm    (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm    (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (KrM m,w) (K   i f) = all (\w' -> eval (KrM m,w') f) (snd (m ! w) ! i)
eval (KrM m,w) (Kw  i f) = alleqWith (\w' -> eval (KrM m,w') f) (snd (m ! w) ! i)
eval (m,w) (Ck ags form) = all (\w' -> eval (m,w') form) (groupRel m ags w)
eval (m,w) (Ckw ags form) = alleqWith (\w' -> eval (m,w') form) (groupRel m ags w)
eval (m,w) (PubAnnounce f g) = not (eval (m,w) f) || eval (pubAnnounceNonS5 m f,w) g
eval (m,w) (PubAnnounceW f g) = eval (pubAnnounceNonS5 m aform, w) g where
  aform | eval (m,w) f = f
        | otherwise     = Neg f
eval (m,w) (Announce listeners f g) = not (eval (m,w) f) || eval newm g where
  newm = (m,w) `productUpdate` announceActionNonS5 (agentsOf m) listeners f
eval (m,w) (AnnounceW listeners f g) = eval newm g where
  newm = (m,w) `productUpdate` announceActionNonS5 (agentsOf m) listeners aform
  aform | eval (m,w) f = f
        | otherwise    = Neg f

groupRel :: KripkeModel -> [Agent] -> World -> [World]
groupRel (KrM m) ags w = lfp extend (oneStepReachFrom w) where
  oneStepReachFrom x = concat [ snd (m ! x) ! a | a <- ags ]
  extend xs = sort . nub $ xs ++ concatMap oneStepReachFrom xs

pubAnnounceNonS5 :: KripkeModel -> Form -> KripkeModel
pubAnnounceNonS5 (KrM m) f = KrM newm where
  newm = mapMaybeWithKey isin m
  isin w' (v,rs) | eval (KrM m,w') f = Just (v,Data.Map.Strict.map newr rs)
                 | otherwise         = Nothing
  newr = filter (`elem` Data.Map.Strict.keys newm)

announceActionNonS5 :: [Agent] -> [Agent] -> Form -> PointedActionModel
announceActionNonS5 everyone listeners f = (AM am, 1) where
  am = fromList
    [ (1, (f  , fromList $ [(i,[1]) | i <- listeners] ++ [(i,[2]) | i <- everyone \\ listeners]))
    , (2, (Top, fromList   [(i,[2]) | i <- everyone]) ) ]

mudGenKrpInit :: Int -> Int -> PointedModel
mudGenKrpInit n m = (KrM $ fromList wlist, cur) where
  wlist = [ (w, (fromList (vals !! w), fromList $ relFor w)) | w <- ws ]
  ws    = [0..(2^n-1)]
  vals  = map sort (foldl buildTable [[]] [P k | k<- [1..n]])
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor w = [ (show i, seesFrom i w) | i <- [1..n] ]
  seesFrom i w = filter (\v -> samefor i (vals !! w) (vals !! v)) ws
  samefor i ps qs = seteq (delete (P i) (map fst $ filter snd ps)) (delete (P i) (map fst $ filter snd qs))
  (Just cur) = elemIndex curVal vals
  curVal = sort $ [(p,True) | p <- [P 1 .. P m]] ++ [(p,True) | p <- [P (m+1) .. P n]]

myMudGenKrpInit :: PointedModel
myMudGenKrpInit = mudGenKrpInit 3 3

generatedSubmodel :: PointedModel -> PointedModel
generatedSubmodel (KrM m, cur) = (KrM newm, cur) where
  newm = mapMaybeWithKey isin m
  isin w' (v,rs) | w' `elem` reachable = Just (v, Data.Map.Strict.map newr rs)
                 | otherwise           = Nothing
  newr = filter (`elem` Data.Map.Strict.keys newm)
  reachable = lfp follow [cur] where
    follow xs = sort . nub $ concat [ snd (m ! x) ! a | x <- xs, a <- agentsOf (KrM m) ]

newtype ActionModel = AM (Map Action (Form, Map Agent [Action]))
  deriving (Eq,Ord,Show)
type PointedActionModel = (ActionModel, Action)

eventsOf :: ActionModel -> [Action]
eventsOf (AM am) = Data.Map.Strict.keys am

instance HasAgents ActionModel where
  agentsOf (AM am) = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems am))

relOfInAM :: Agent -> ActionModel -> Map Action [Action]
relOfInAM i (AM am) = Data.Map.Strict.map (\x -> snd x ! i) am

instance KripkeLike PointedActionModel where
  directed = const True
  getNodes (AM am, _) = map (show &&& labelOf) (eventsOf (AM am)) where
    labelOf a = "$" ++ tex (fst $ am ! a) ++ "$"
  getEdges (AM am, _) = concat [ [ (a,show w,show v) | v <- relOfInAM a (AM am) ! w ] | w <- eventsOf (AM am), a <- agentsOf (AM am) ]
  getActuals (_, cur) = [show cur]
  nodeAts _ True  = [shape BoxShape, style solid]
  nodeAts _ False = [shape BoxShape, style dashed]

instance TexAble PointedActionModel where tex = tex.ViaDot

productUpdate :: PointedModel -> PointedActionModel -> PointedModel
productUpdate (KrM m, oldcur) (AM am, act)
  | agentsOf (KrM m) /= agentsOf (AM am)    = error "productUpdate failed: Agents of KrM and GAM are not the same!"
  | not $ eval (KrM m, oldcur) (fst $ am ! act) = error "productUpdate failed: Actual precondition is false!"
  | otherwise = (KrM $ fromList (map annotate statePairs), newcur) where
    statePairs = zip [ (s, a) | s <- worldsOf (KrM m), a <- eventsOf (AM am), eval (KrM m, s) (fst $ am ! a) ] [0..]
    annotate ((s,a),news) = (news , (fst $ m ! s, fromList (map reachFor (agentsOf (KrM m))))) where
      reachFor i = (i, [ news' | ((s',a'),news') <- statePairs, s' `elem` snd (m !  s) ! i, a' `elem` snd (am ! a) ! i ])
    (Just newcur) = lookup (oldcur,act) statePairs

-- Privately tell alice that P 0, while bob thinks nothing happens.
exampleGenActM :: ActionModel
exampleGenActM = AM $ fromList
  [ (1, (PrpF (P 0), fromList [(alice,[1]), (bob,[2])] ) )
  , (2, (Top       , fromList [(alice,[2]), (bob,[2])] ) ) ]

examplePointedActM :: PointedActionModel
examplePointedActM = (exampleGenActM,1)

exampleResult :: PointedModel
exampleResult = productUpdate examplePointedModel examplePointedActM
