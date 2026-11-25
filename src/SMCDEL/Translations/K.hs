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
import SMCDEL.Symbolic.S5 (boolBddOf,booloutof,bddEval)
import SMCDEL.Other.BDD2Form
import SMCDEL.Translations.S5 (StateMap)

-- * From Belief Structures to Kripke Models

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

-- | Like `blsToKripke` but also return the function \(g\).
blsToKripkeWithG :: BelStruct -> (KripkeModel, StateMap)
blsToKripkeWithG f@(BlS _ _ obdds) = (m, g) where
  links = zip (statesOf f) [0..]
  m = KrM $ M.fromList
    [ (w, ( M.fromList [(p, p `elem` s) | p <- vocabOf f]
          , M.fromList [(a, map (apply links) $ reachFromFor s a) | a <- agentsOf f] ) )
    | (s,w) <- links ]
  reachFromFor s a = filter (\t -> tagBddEval (mv s ++ cp t) (obdds ! a)) (statesOf f)
  g w    = statesOf f !! w

-- | Like `blsToKripke` but for multipointed structures.
blsToKripkeMulti :: MultipointedBelScene -> MultipointedModel
blsToKripkeMulti (f, statesBdd) = (m, ws) where
  (m, g) = blsToKripkeWithG f
  ws = filter (\w -> evaluateFun statesBdd (\k -> P k `elem` g w)) (worldsOf m)

-- * From Kripke Models to Belief Structures

-- | Convert a pointed Kripke model to a belief scene.
kripkeToBls :: PointedModel -> BelScene
kripkeToBls (m,w)
  | distinctVal m = (kripkeToBlsUnsafe m, truthsInAt m w)
  | otherwise     = let m' = ensureDistinctVal m
                    in (kripkeToBlsUnsafe m', truthsInAt m' w)

-- | Convert a pointed Kripke model to a belief scene.
kripkeToBlsMulti :: MultipointedModel -> MultipointedBelScene
kripkeToBlsMulti (m, curWorlds) =
  let m' = if distinctVal m then m else ensureDistinctVal m
  in ( kripkeToBlsUnsafe m'
     , disSet [ booloutof (truthsInAt m w) (vocabOf m) | w <- curWorlds ] )

-- | Convert a Kripke model to a belief scene, assuming we already have distinct valuations.
kripkeToBlsUnsafe :: KripkeModel -> BelStruct
kripkeToBlsUnsafe m = BlS vocab lawbdd obdds where
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
However, this also includes bisimilar worlds which we would not want to be distinguished anyway.
Hence the input model should first be minimized and then converted.
Alternatively, the output structure can be optimized after the conversion.

-}

-- | If necessary, use extra proposition letters to ensure distinct valuations.
ensureDistinctVal :: KripkeModel -> KripkeModel
ensureDistinctVal krm@(KrM m) = if distinctVal krm then krm else KrM newM where
  sameVals = groupSortWith (truthsInAt krm) (worldsOf krm)
  indexOf w = let k = fromJust $ elemIndex w (head $ filter (elem w) sameVals) in k
  numAddProps = ceiling $ logBase (2::Double) (fromIntegral $ maximum (map length sameVals) + 1)
  addProps = take numAddProps [freshp (vocabOf krm) ..]
  addValForIndex k = M.fromList [ (p, p `elem` (reverse (powerset addProps) !! k) ) | p <- addProps ]
  newM = M.mapWithKey (\w (val,r) -> (M.union val (addValForIndex (indexOf w)),r)) m

-- * From Action Models to Transformers

-- | Convert an action model to a transformer, also returning the $$\ell$$ labelling.
-- Note that we don't need extra propositions for the action relation any longer.
actionToTrfWithEll :: ActionModel -> (Transformer, StateMap)
actionToTrfWithEll (ActM am) = (Trf addprops addlaw changelaw eventObs, ell) where
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

-- | Convert a pointed action model to a symbolic event.
actionToEvent :: PointedActionModel -> Event
actionToEvent (am, faction) = (trf, efacts) where
  (trf, ell) = actionToTrfWithEll am
  efacts     = ell faction

-- | Convert a pointed action model to a symbolic event.
actionToEventMulti :: MultipointedActionModel -> MultipointedEvent
actionToEventMulti (am, curActions) = (trf, curActionsLaw) where
  (trf@(Trf addprops _ _ _), ell) = actionToTrfWithEll am
  curActionsLaw = disSet [ booloutof (ell w) addprops | w <- curActions ]

-- * From Transformers to Action Models

trfToActionWithG :: Transformer -> (ActionModel, StateMap)
trfToActionWithG t@(Trf addprops addlaw changelaw eventObs) = (ActM am, g) where
  actlist    = zip (powerset addprops) [0..]
  am         = M.fromList [ (a, Act (preFor ps) (PC $ postFor ps) (relFor ps)) | (ps,a) <- actlist ]
  preFor ps  = simplify $ substitSet (map (, Top) ps ++ map (, Bot) (addprops \\ ps)) addlaw
  postFor ps = M.fromList [ (q, formOf $ (changelaw ! q) `restrictSet` [(p, P p `elem` ps) | (P p) <- addprops]) | q <- M.keys changelaw ]
  relFor ps  = M.fromList [(i,rFor i) | i <- agentsIn t] where
    rFor i   = concatMap (\(qs,b) -> [ b | tagBddEval (mv ps ++ cp qs) (eventObs ! i), preFor qs /= Bot ]) actlist
  g :: StateMap
  g a = head [ x | (x, a') <- actlist, a' == a ]

eventToAction :: Event -> PointedActionModel
eventToAction (trf, event) = (ActM am, faction) where
  (ActM am, g) = trfToActionWithG trf
  acts = M.keys am
  faction = case [ a | a <- acts, g a == event ] of
    [fct] -> fct
    _ -> error $ unlines
      [ "Could not find faction:"
      , "  acts = " ++ show am
      , "  map g acts = " ++ show (map g acts)
      , "  event = " ++ show event
      , "  trf = " ++ show trf
      ]

eventToActionMulti :: MultipointedEvent -> MultipointedActionModel
eventToActionMulti (trf, actualEventLaw) = (ActM am, factions) where
  (ActM am, g) = trfToActionWithG trf
  factions = [ a | a <- M.keys am, bddEval (g a) actualEventLaw ]
