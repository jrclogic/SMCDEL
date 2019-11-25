{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module SMCDEL.Translations.Convert where

import qualified Data.Map.Strict as M

import SMCDEL.Language (agentsOf)
import SMCDEL.Internal.Help
import SMCDEL.Explicit.K
import SMCDEL.Explicit.S5
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5

class Convertable a b where
  convert :: a -> b

instance Convertable PointedModelS5 PointedModel where
  convert s5m@(KrMS5 worlds rels vals, cur) = (KrM m, cur) where
    m = M.fromList [ (w,(valFor w, relsFor w)) | w <- worlds ]
    valFor w = M.fromList (vals ! w)
    relsFor w = M.fromList [(i, concat $ filter (elem w) (rels ! i))
                           | i <- agentsOf s5m ]

instance Convertable KnowScene BelScene where
  convert (KnS voc law obs, s) = (BlS voc law obsLaws, s) where
    obsLaws = M.fromList [ (i, allsamebdd ob) | (i,ob) <- obs ]
