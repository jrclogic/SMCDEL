{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- | This module provides conversion from S5 models and structures to their more general K equivalents.
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

-- | Every S5 Kripke model is also a general Kripke model.
-- This replaces each partition \(\sim_i\) with a relation \(R_i\).
instance Convertable PointedModelS5 PointedModel where
  convert s5m@(KrMS5 worlds rels vals, cur) = (KrM m, cur) where
    m = M.fromList [ (w,(valFor w, relsFor w)) | w <- worlds ]
    valFor w = M.fromList (vals ! w)
    relsFor w = M.fromList [(i, concat $ filter (elem w) (rels ! i))
                           | i <- agentsOf s5m ]

-- | Every knowledge structure is also a belief structure.
-- We replace each \(O_i\) with \(\Omega_i := \bigwedge_{p \in O_i} (p \leftrightarrow p')\).
instance Convertable KnowScene BelScene where
  convert (KnS voc law obs, s) = (BlS voc law obsLaws, s) where
    obsLaws = M.fromList [ (i, allsamebdd ob) | (i,ob) <- obs ]
