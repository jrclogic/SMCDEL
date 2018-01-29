
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TypeOperators #-}

module SMCDEL.Translations.K where

import Data.HasCacBDD hiding (Top,Bot)
import Data.Map.Strict (Map,fromList,(!))

import SMCDEL.Language
import SMCDEL.Symbolic.S5 (State)
import SMCDEL.Explicit.S5 (worldsOf)

import SMCDEL.Symbolic.K
import SMCDEL.Explicit.K
import SMCDEL.Translations.S5 (booloutof)
import SMCDEL.Internal.Help (apply)

blsToKripke :: BelScene -> PointedModel
blsToKripke (f@(BlS _ _ obdds), curs) = (m, cur) where
  links = zip (statesOf f) [0..]
  m = KrM $ fromList
    [ (w, ( fromList [(p, p `elem` s) | p <- vocabOf f]
          , fromList [(a, map (apply links) $ reachFromFor s a) | a <- agentsOf f] ) )
    | (s,w) <- links ]
  reachFromFor s a = filter (\t -> tagBddEval (mv s ++ cp t) (obdds ! a)) (statesOf f)
  (Just cur) = lookup curs links

kripkeToBls :: PointedModel -> BelScene
kripkeToBls (m, cur) = (BlS vocab lawbdd obdds, truthsInAt m cur) where
  vocab  = vocabOf m
  lawbdd = disSet [ booloutof (truthsInAt m w) vocab | w <- worldsOf m ]
  obdds  :: Map Agent RelBDD
  obdds  = fromList [ (i, restrictLaw <$> relBddOfIn i m <*> (con <$> mvBdd lawbdd <*> cpBdd lawbdd)) | i <- agents ]
  agents = agentsOf m

exampleBelScn :: BelScene
exampleBelScn = kripkeToBls examplePointedModel

exampleBelStruct :: BelStruct
exampleBelState :: State
(exampleBelStruct,exampleBelState) = exampleBelScn
