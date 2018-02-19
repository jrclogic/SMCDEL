{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Translations.K.Change where

import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),nub,sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!),fromList)

import SMCDEL.Explicit.K.Change
import SMCDEL.Internal.Help (apply,powerset)
import SMCDEL.Language
import SMCDEL.Translations.S5 (booloutof)
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.K.Change
import SMCDEL.Symbolic.S5 (boolBddOf)

actionToEvent :: PointedChangeModel -> Event
actionToEvent (ChM chm, faction) = (Trf addprops addlaw changeprops changelaw eventObs, efacts) where
  actions      = M.keys chm
  (P fstnewp)  = freshp $ concatMap -- avoid props in pre and postconditions
    (\c -> propsInForms (pre c : M.elems (post c)) ++ M.keys (post c)) (M.elems chm)
  addprops     = [P fstnewp..P maxactprop] -- new props to distinguish all actions
  maxactprop   = fstnewp + ceiling (logBase 2 (fromIntegral $ length actions) :: Float) - 1
  ell          = apply $ zip actions (powerset addprops) -- injectively label actions with sets of propositions
  addlaw       = simplify $ Disj [ Conj [ booloutofForm (ell a) addprops, pre $ chm ! a ] | a <- actions ]
  changeprops  = sort $ nub $ concatMap M.keys . M.elems $ M.map post chm -- propositions to be changed
  changelaw    = M.fromList [ (p, changeFor p) | p <- changeprops ] -- encode postconditions
  changeFor p  = disSet [ booloutof (ell k) addprops `con` boolBddOf (safepost (chm ! k) p) | k <- actions ]
  eventObs     = M.fromList [ (i, obsLawFor i) | i <- agentsOf (ChM chm) ]
  obsLawFor i  = pure $ disSet (M.elems $ M.mapWithKey (link i) chm)
  link i k ch  = booloutof (mv $ ell k) (mv addprops) `con` -- encode relations
                 disSet [ booloutof (cp $ ell there) (cp addprops) | there <- rel ch ! i ]
  efacts       = ell faction

eventToAction' :: Event -> PointedChangeModel
eventToAction' (t@(Trf addprops addlaw changeprops changelaw eventObs), efacts) = (ChM chm, faction) where
  actlist    = zip (powerset addprops) [0..]
  chm        = fromList [ (a, Ch (preFor ps) (postFor ps) (relFor ps)) | (ps,a) <- actlist ]
  preFor ps  = simplify $
    substitSet (zip ps (repeat Top) ++ zip (addprops \\ ps) (repeat Bot)) addlaw
  postFor ps = fromList
    [ (q, formOf $ restrictSet (changelaw ! q) [(p, P p `elem` ps) | (P p) <- addprops]) | q <- changeprops ]
  relFor ps = fromList [(i,rFor i) | i <- agentsOf t] where
    rFor i = concatMap (\(qs,b) -> [ b | tagBddEval (mv ps ++ cp qs) (eventObs ! i) ]) actlist
  faction   = apply actlist efacts

