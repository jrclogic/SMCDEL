{-# LANGUAGE FlexibleInstances, TupleSections #-}

{- |

Converting between Kripke Models and Belief Structures.

-}

module SMCDEL.Translations.K where

import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),elemIndex,nub,sort)
import Data.Maybe (fromJust)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M

import SMCDEL.Language
import SMCDEL.Explicit.S5 (worldsOf)
import SMCDEL.Explicit.K
import SMCDEL.Internal.Help (apply,powerset,groupSortWith)
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (boolBddOf,booloutof)
import SMCDEL.Other.BDD2Form

-- | Convert a belief scene to a pointed Kripke model.
blsToKripke :: BelScene -> PointedModel
blsToKripke (f@(BlS _ _ obdds), curs) = (m, cur) where
  links = zip (statesOf f) [0..]
  m = KrM $ M.fromList
    [ (w, ( M.fromList [(p, p `elem` s) | p <- vocabOf f]
          , M.fromList [(a, map (apply links) $ reachFromFor s a) | a <- agentsOf f] ) )
    | (s,w) <- links ]
  reachFromFor s a = filter (\t -> tagBddEval (mv s ++ cp t) (obdds ! a)) (statesOf f)
  cur = fromJust (lookup curs links)

-- * From Kripke Models to Belief Structures

kripkeToBls :: PointedModel -> BelScene
kripkeToBls pm@(m,_) | distinctVal m = kripkeToBlsUnsafe pm
                     | otherwise     = kripkeToBlsUnsafe (ensureDistinctVal pm)

-- | Unsafe version of `kripkeToBls`, assuming we already have distinct valuations.
kripkeToBlsUnsafe :: PointedModel -> BelScene
kripkeToBlsUnsafe (m, cur) = (BlS vocab lawbdd obdds, truthsInAt m cur) where
  vocab  = vocabOf m
  lawbdd = disSet [ booloutof (truthsInAt m w) vocab | w <- worldsOf m ]
  obdds  :: M.Map Agent RelBDD
  obdds  = M.fromList [ (i, restrictLaw <$> relBddOfIn i m <*> (con <$> mvBdd lawbdd <*> cpBdd lawbdd)) | i <- agents ]
  agents = agentsOf m

{- $

If valuations are not unique, we need to add propositions.
This can be done in different ways, leading to different numbers of propositions to be added.
In the method below, if there maximally \(k\) many worlds with the same valuation, then we add \(\log_2 k\) many new atomic propositions.
This is optimal in the sense that less propositions will not be enough to distinguish all worlds.
However, this also includes bisimilar worlds which we would not want to be distignuished anyway.
Hence the input model should first be minimized and then converted.
Alternatively, the output structure can be optimized after the conversion.

-}

ensureDistinctVal :: PointedModel -> PointedModel
ensureDistinctVal (krm@(KrM m), cur) = if distinctVal krm then (krm,cur) else (KrM newM,cur) where
  sameVals = groupSortWith (truthsInAt krm) (worldsOf krm)
  indexOf w = let k = fromJust $ elemIndex w (head $ filter (elem w) sameVals) in k
  numAddProps = ceiling $ logBase (2::Double) (fromIntegral $ maximum (map length sameVals) + 1)
  addProps = take numAddProps [freshp (vocabOf krm) ..]
  addValForIndex k = M.fromList [ (p, p `elem` (reverse (powerset addProps) !! k) ) | p <- addProps ]
  newM = M.mapWithKey (\w (val,r) -> (M.union val (addValForIndex (indexOf w)),r)) m

-- * From Action Models to Transformers

-- | This generalizes `SMCDEL.Translations.S5.actionToEvent``
-- Note that we don't need extra propositions for the action relation any longer.
actionToEvent :: PointedActionModel -> Event
actionToEvent (ActM am, faction) = (Trf addprops addlaw changelaw eventObs, efacts) where
  actions      = M.keys am
  (P fstnewp)  = freshp $ concatMap -- avoid props in pre and postconditions
                 (\c -> propsIn (pre c : M.elems (postmap c)) ++ M.keys (postmap c)) (M.elems am)
  addprops     = [P fstnewp..P maxactprop] -- new props to distinguish all actions
  maxactprop   = fstnewp + ceiling (logBase 2 (fromIntegral $ length actions) :: Float) - 1
  ell          = apply $ zip actions (powerset addprops) -- injectively label actions with sets of propositions
  addlaw       = simplify $ Disj [ Conj [ booloutofForm (ell a) addprops, pre $ am ! a ] | a <- actions ]
  changeprops  = sort $ nub $ concatMap M.keys . M.elems $ M.map postmap am -- propositions to be changed
  changelaw    = M.fromList [ (p, changeFor p) | p <- changeprops ] -- encode postconditions
  changeFor p  = disSet [ booloutof (ell k) addprops `con` boolBddOf (safepost (am ! k) p) | k <- actions ]
  eventObs     = M.fromList [ (i, obsLawFor i) | i <- agentsIn (ActM am) ]
  obsLawFor i  = pure $ disSet (M.elems $ M.mapWithKey (link i) am)
  link i k ch  = booloutof (mv $ ell k) (mv addprops) `con` -- encode relations
                 disSet [ booloutof (cp $ ell there) (cp addprops) | there <- rel ch ! i ]
  efacts       = ell faction

-- * From Transformers to Action Models

eventToAction :: Event -> PointedActionModel
eventToAction (t@(Trf addprops addlaw changelaw eventObs), efacts) = (ActM am, faction) where
  actlist    = zip (powerset addprops) [0..]
  am         = M.fromList [ (a, Act (preFor ps) (PC $ postFor ps) (relFor ps)) | (ps,a) <- actlist ]
  preFor ps  = simplify $ substitSet (map (, Top) ps ++ map (, Bot) (addprops \\ ps)) addlaw
  postFor ps = M.fromList [ (q, formOf $ (changelaw ! q) `restrictSet` [(p, P p `elem` ps) | (P p) <- addprops]) | q <- M.keys changelaw ]
  relFor ps  = M.fromList [(i,rFor i) | i <- agentsIn t] where
    rFor i   = concatMap (\(qs,b) -> [ b | tagBddEval (mv ps ++ cp qs) (eventObs ! i), preFor qs /= Bot ]) actlist
  faction    = apply actlist efacts

-- TODO unpointed and multipointed translations
