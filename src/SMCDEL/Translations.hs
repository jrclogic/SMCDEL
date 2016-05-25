
module SMCDEL.Translations where
import Control.Arrow (second)
import Data.List (groupBy,sort,(\\),elemIndex,intersect)
import Data.Maybe (fromJust)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD
import SMCDEL.Explicit.Simple
import SMCDEL.Internal.Help (anydiff,alldiff,alleq,apply,powerset)

import Data.HasCacBDD hiding (Top,Bot)

knsToKripke :: Scenario -> PointedModel
knsToKripke (kns@(KnS ps _ obs),curs) =
  if curs `elem` statesOf kns
     then (KrM worlds rel val, cur)
     else error "knsToKripke failed: Invalid state."
  where
    lav    = zip (statesOf kns) [0..(length (statesOf kns)-1)]
    val    = map ( \(s,n) -> (n,state2kripkeass s) ) lav where
      state2kripkeass s = map (\p -> (p, p `elem` s)) ps
    rel    = [(i,rfor i) | i <- map fst obs]
    rfor i = map (map snd) (groupBy ( \ (x,_) (y,_) -> x==y ) (sort pairs)) where
      pairs = map (\s -> (restrictState s (apply obs i), apply lav s)) (statesOf kns)
    worlds = map fst val
    cur    = apply lav curs

kripkeToKns :: PointedModel -> Scenario
kripkeToKns (KrM worlds rel val, cur) = (KnS ps law obs, curs) where
  v         = map fst $ apply val cur
  ags       = map fst rel
  newpstart = fromEnum $ freshp v -- start counting new propositions here
  amount i  = ceiling (logBase 2 (fromIntegral $ length (apply rel i)) :: Float) -- |O_i|
  newpstep  = maximum [ amount i | i <- ags ]
  numberof i = fromJust $ elemIndex i (map fst rel)
  newps i   = map (\k -> P (newpstart + (newpstep * numberof i) +k)) [0..(amount i - 1)] -- O_i
  copyrel i = zip (apply rel i) (powerset (newps i)) -- label equiv.classes with P(O_i)
  gag i w   = snd $ head $ filter (\(ws,_) -> elem w ws) (copyrel i)
  g w       = filter (apply (apply val w)) v ++ concat [ gag i w | i <- ags ]
  ps        = v ++ concat [ newps i | i <- ags ]
  law       = disSet [ booloutof (g w) ps | w <- worlds ]
  obs       = [ (i,newps i) | i<- ags ]
  curs      = sort $ g cur

booloutof :: [Prp] -> [Prp] -> Bdd
booloutof ps qs = conSet $
  [ var n | (P n) <- ps ] ++
  [ neg $ var n | (P n) <- qs \\ ps ]

uniqueVals :: KripkeModel -> Bool
uniqueVals (KrM _ _ val) = alldiff (map snd val)

voc :: KripkeModel -> [Prp]
voc (KrM _ _ val) = map fst . snd . head $ val

-- | Get lists of variables which agent i does (not) observe
-- in model m. This does *not* preserve all information, i.e.
-- does not characterize every possible S5 relation!
obsnobs :: KripkeModel -> Agent -> ([Prp],[Prp])
obsnobs m@(KrM _ rel val) i = (obs,nobs) where
  propsets = map (map (map fst . filter snd . apply val)) (apply rel i)
  obs = filter (\p -> all (alleq (elem p)) propsets) (voc m)
  nobs = filter (\p -> any (anydiff (elem p)) propsets) (voc m)

-- | Test if all relations can be described using observariables.
descableRels :: KripkeModel -> Bool
descableRels m@(KrM ws rel val) = all descable (map fst rel) where
  wpairs = [ (v,w) | v <- ws, w <- ws ]
  descable i = cover && correct where
    (obs,nobs) = obsnobs m i
    cover = sort (voc m) == sort (obs ++ nobs) -- implies disjointness
    correct = all (\pair -> oldrel pair == newrel pair) wpairs
    oldrel (v,w) = v `elem` head (filter (elem w) (apply rel i))
    newrel (v,w) = (factsAt v `intersect` obs) == (factsAt w `intersect` obs)
    factsAt w = map fst $ filter snd $ apply val w

-- | Try to find an equivalent knowledge structure without
-- additional propositions. Will succeed iff valuations are
-- unique and relations can be described using observariables.
smartKripkeToKns :: PointedModel -> Maybe Scenario
smartKripkeToKns (m, cur) =
  if uniqueVals m && descableRels m
    then Just (smartKripkeToKnsWithoutChecks (m, cur))
    else Nothing

smartKripkeToKnsWithoutChecks :: PointedModel -> Scenario
smartKripkeToKnsWithoutChecks (m@(KrM worlds rel val), cur) =
  (KnS ps law obs, curs) where
    ps = voc m
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
  actforms     = [ Impl (booloutofForm (apply copyactprops a) actionprops) (apply precon a) | a <- actions ] -- connect the new propositions to the preconditions
  actrelprops  = concat [ newps i | i <- ags ] -- new props to distinguish actions for i
  actrelpstart = maxactprop + 1
  numberof i = fromJust $ elemIndex i (map fst actrel)
  newps i      = map (\k -> P (actrelpstart + (newpstep * numberof i) +k)) [0..(amount i - 1)]
  amount i     = ceiling (logBase 2 (fromIntegral $ length (apply actrel i)) :: Float)
  newpstep     = maximum [ amount i | i <- ags ]
  copyactrel i = zip (apply actrel i) (powerset (newps i)) -- actrelprops <-> actionprops
  actrelfs i   = [ Impl (booloutofForm (apply (copyactrel i) as) (newps i)) (Disj [adesc a|a<-as]) | as <- apply actrel i ] where adesc a = booloutofForm (apply copyactprops a) actionprops
  actrelforms  = concatMap actrelfs ags
  factsFor i   = snd $ head $ filter (\(as,_) -> elem faction as) (copyactrel i)
  efacts       = apply copyactprops faction ++ concatMap factsFor ags
  elaw         = simplify $ Conj (actforms ++ actrelforms)
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
