
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes #-}

module SMCDEL.Other.Planning where

import SMCDEL.Language

type OfflinePlan = [(Form,Form)] -- list of (announcement,goal) tuples

class Plan a where
  succeeds :: a -> Form

instance Plan OfflinePlan where
  succeeds [] = Top
  succeeds ((step,goal):rest) =
    Conj [step, PubAnnounce step goal, PubAnnounce step (succeeds rest)]

succeedsOn :: (Semantics o, Plan a) => a -> o -> Bool
succeedsOn plan start = isTrue start (succeeds plan)

data OnlinePlan = Stop | DoAnnounce Form OnlinePlan | IfThenElse Form OnlinePlan OnlinePlan

instance Plan OnlinePlan where
  succeeds Stop = Top
  succeeds (DoAnnounce step next) = Conj [step, PubAnnounce step (succeeds next)]
  succeeds (IfThenElse check planA planB) =
    Conj [ check `Impl` succeeds planA, Neg check `Impl` succeeds planB ]
