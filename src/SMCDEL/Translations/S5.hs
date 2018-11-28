module SMCDEL.Translations.S5 where

import Control.Arrow (second)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (groupBy,sort,(\\),elemIndex,intersect,nub)
import Data.Maybe (listToMaybe)
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Explicit.S5
import SMCDEL.Internal.Help (anydiffWith,alldiff,alleqWith,apply,powerset,(!),seteq,subseteq)

type StateMap = World -> State

equivalentWith :: PointedModelS5 -> KnowScene -> StateMap -> Bool
equivalentWith (KrMS5 ws rel val, actw) (kns@(KnS _ _ obs), curs) g =
  c1 && c2 && c3 && g actw == curs where
    c1 = all (\l -> knsLink l == kriLink l) linkSet where
      linkSet = nub [ (i,w1,w2) | w1 <- ws, w2 <- ws, w1 <= w2, i <- map fst rel ]
      knsLink (i,w1,w2) = let oi = obs ! i in (g w1 `intersect` oi) `seteq` (g w2 `intersect` oi)
      kriLink (i,w1,w2) = any (\p -> w1 `elem` p && w2 `elem` p) (rel ! i)
    c2 = and [ (p `elem` g w) == ((val ! w) ! p) | w <- ws, p <- map fst (snd $ head val) ]
    c3 = statesOf kns `seteq` nub (map g ws)

findStateMap :: PointedModelS5 -> KnowScene -> Maybe StateMap
findStateMap pm@(KrMS5 _ _ val, w) scn@(kns, s)
  | vocabOf pm `subseteq` vocabOf kns = listToMaybe goodMaps
  | otherwise = error "vocabOf pm not subseteq vocabOf kns"
  where
    extraProps = vocabOf kns \\ vocabOf pm
    allFuncs :: Eq a => [a] -> [b] -> [a -> b]
    allFuncs []     _  = [ const undefined ]
    allFuncs (x:xs) ys = [ \a -> if a == x then y else f a | y <- ys, f <- allFuncs xs ys ]
    allMaps, goodMaps :: [StateMap]
    baseMap  = map fst . filter snd . (val !)
    allMaps  = [ \v -> baseMap v ++ restf v | restf <- allFuncs (worldsOf pm) (powerset extraProps) ]
    goodMaps = filter (\g -> g w == s && equivalentWith pm scn g) allMaps

knsToKripke :: KnowScene -> PointedModelS5
knsToKripke = fst . knsToKripkeWithG

knsToKripkeWithG :: KnowScene -> (PointedModelS5, StateMap)
knsToKripkeWithG (kns@(KnS ps _ obs),curs) =
  if curs `elem` statesOf kns
     then ((KrMS5 worlds rel val, cur) , g)
     else error "knsToKripke failed: Invalid state."
  where
    lav    = zip (statesOf kns) [0..(length (statesOf kns)-1)]
    val    = map ( \(s,n) -> (n,state2kripkeass s) ) lav where
      state2kripkeass s = map (\p -> (p, p `elem` s)) ps
    rel    = [(i,rfor i) | i <- map fst obs]
    rfor i = map (map snd) (groupBy ( \ (x,_) (y,_) -> x==y ) (sort pairs)) where
      pairs = map (\s -> (restrictState s (obs ! i), lav ! s)) (statesOf kns)
    worlds = map snd lav
    cur    = lav ! curs
    g w    = statesOf kns !! w

kripkeToKns :: PointedModelS5 -> KnowScene
kripkeToKns = fst . kripkeToKnsWithG

kripkeToKnsWithG :: PointedModelS5 -> (KnowScene, StateMap)
kripkeToKnsWithG (KrMS5 worlds rel val, cur) = ((KnS ps law obs, curs), g) where
  v         = map fst (val ! cur)
  ags       = map fst rel
  newpstart = fromEnum $ freshp v -- start counting new propositions here
  amount i  = ceiling (logBase 2 (fromIntegral $ length (rel ! i)) :: Float) -- = |O_i|
  newpstep  = maximum [ amount i | i <- ags ]
  newps i   = map (\k -> P (newpstart + (newpstep * inum) +k)) [0..(amount i - 1)] -- O_i
    where (Just inum) = elemIndex i (map fst rel)
  copyrel i = zip (rel ! i) (powerset (newps i)) -- label equiv.classes with P(O_i)
  gag i w   = snd $ head $ filter (\(ws,_) -> elem w ws) (copyrel i)
  g w       = filter (apply (val ! w)) v ++ concat [ gag i w | i <- ags ]
  ps        = v ++ concat [ newps i | i <- ags ]
  law       = disSet [ booloutof (g w) ps | w <- worlds ]
  obs       = [ (i,newps i) | i<- ags ]
  curs      = sort $ g cur

booloutof :: [Prp] -> [Prp] -> Bdd
booloutof ps qs = conSet $
  [ var n | (P n) <- ps ] ++
  [ neg $ var n | (P n) <- qs \\ ps ]

uniqueVals :: KripkeModelS5 -> Bool
uniqueVals (KrMS5 _ _ val) = alldiff (map snd val)

-- | Get lists of variables which agent i does (not) observe
-- in model m. This does *not* preserve all information, i.e.
-- does not characterize every possible S5 relation!
obsnobs :: KripkeModelS5 -> Agent -> ([Prp],[Prp])
obsnobs m@(KrMS5 _ rel val) i = (obs,nobs) where
  propsets = map (map (map fst . filter snd . apply val)) (apply rel i)
  obs = filter (\p -> all (alleqWith (elem p)) propsets) (vocabOf m)
  nobs = filter (\p -> any (anydiffWith (elem p)) propsets) (vocabOf m)

-- | Test if all relations can be described using observariables.
descableRels :: KripkeModelS5 -> Bool
descableRels m@(KrMS5 ws rel val) = all descable (map fst rel) where
  wpairs = [ (v,w) | v <- ws, w <- ws ]
  descable i = cover && correct where
    (obs,nobs) = obsnobs m i
    cover = sort (vocabOf m) == sort (obs ++ nobs) -- implies disjointness
    correct = all (\pair -> oldrel pair == newrel pair) wpairs
    oldrel (v,w) = v `elem` head (filter (elem w) (apply rel i))
    newrel (v,w) = (factsAt v `intersect` obs) == (factsAt w `intersect` obs)
    factsAt w = map fst $ filter snd $ apply val w

-- | Try to find an equivalent knowledge structure without
-- additional propositions. Will succeed iff valuations are
-- unique and relations can be described using observariables.
smartKripkeToKns :: PointedModelS5 -> Maybe KnowScene
smartKripkeToKns (m, cur) =
  if uniqueVals m && descableRels m
    then Just (smartKripkeToKnsWithoutChecks (m, cur))
    else Nothing

smartKripkeToKnsWithoutChecks :: PointedModelS5 -> KnowScene
smartKripkeToKnsWithoutChecks (m@(KrMS5 worlds rel val), cur) =
  (KnS ps law obs, curs) where
    ps = vocabOf m
    g w = filter (apply (apply val w)) ps
    law = disSet [ booloutof (g w) ps | w <- worlds ]
    obs = map (\(i,_) -> (i,obsOf i) ) rel
    obsOf = fst.obsnobs m
    curs = map fst $ filter snd $ apply val cur

actionToEvent :: PointedActionModel -> Event
actionToEvent (ActM actions precon actrel, faction) = (KnT eprops elaw eobs, efacts) where
  ags          = map fst actrel
  eprops       = actionprops ++ actrelprops
  (P fstnewp)  = freshp $ propsInForms (map snd precon)
  actionprops  = [P fstnewp..P maxactprop] -- new props to distinguish all actions
  maxactprop   = fstnewp + ceiling (logBase 2 (fromIntegral $ length actions) :: Float) -1
  copyactprops = zip actions (powerset actionprops)
  ell          = apply copyactprops -- label actions with subsets of actionprops
  happens a    = booloutofForm (ell a) actionprops -- boolean formula to say that a happens
  actform      = Disj [ Conj [ happens a, apply precon a ] | a <- actions ] -- connect new propositions to preconditions
  actrelprops  = concat [ newps i | i <- ags ] -- new props to distinguish actions for i
  actrelpstart = maxactprop + 1
  newps i      = map (\k -> P (actrelpstart + (newpstep * inum) +k)) [0..(amount i - 1)]
    where (Just inum) = elemIndex i (map fst actrel)
  amount i     = ceiling (logBase 2 (fromIntegral $ length (apply actrel i)) :: Float)
  newpstep     = maximum [ amount i | i <- ags ]
  copyactrel i = zip (apply actrel i) (powerset (newps i)) -- label equclasses-of-actions with subsets-of-newps
  actrelfs i   = [ Equi (booloutofForm (apply (copyactrel i) as) (newps i)) (Disj (map happens as)) | as <- apply actrel i ]
  actrelforms  = concatMap actrelfs ags
  factsFor i   = snd $ head $ filter (\(as,_) -> elem faction as) (copyactrel i)
  efacts       = apply copyactprops faction ++ concatMap factsFor ags
  elaw         = simplify $ Conj (actform : actrelforms)
  eobs         = [ (i,newps i) | i<- ags ]

eventToAction' :: Event -> PointedActionModel
eventToAction' (KnT eprops eform eobs, efacts) = (ActM actions precon actrel, faction) where
  actions   = [0..(2 ^ length eprops - 1)]
  actlist   = zip (powerset eprops) actions
  precon    = [ (a, simplify $ preFor ps) | (ps,a) <- actlist ] where
    preFor ps = substitSet (zip ps (repeat Top) ++ zip (eprops\\ps) (repeat Bot)) eform
  actrel    = [(i,rFor i) | i <- map fst eobs] where
    rFor i  = map (map snd) (groupBy ( \ (x,_) (y,_) -> x==y ) (pairs i))
    pairs i = sort $ map (\(set,a) -> (restrictState set $ apply eobs i,a)) actlist
  faction   = apply actlist efacts

eventToAction :: Event -> PointedActionModel
eventToAction (KnT eprops eform eobs, efacts) = (ActM actions precon actrel, faction) where
  (ActM _ precon' actrel', faction) = eventToAction' (KnT eprops eform eobs, efacts)
  precon  = filter (\(_,f) -> f/=Bot) precon' -- remove actions w/ contradictory precon
  actions = map fst precon
  actrel  = map (second fltr) actrel'
  fltr r  = filter ([]/=) $ map (filter (`elem` actions)) r
