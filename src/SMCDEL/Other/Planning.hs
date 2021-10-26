{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module SMCDEL.Other.Planning where

import Data.Dynamic
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (intersect,nub,sort,(\\))
import qualified Data.Map as M

import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5 as Sym
import qualified SMCDEL.Symbolic.K as SymK
import qualified SMCDEL.Explicit.S5 as Exp
import qualified SMCDEL.Explicit.K as ExpK

type OfflinePlan = [Form] -- list of announcements to be made

class IsPlan a where
  reaches :: a -> Form -> Form
  reachesOn :: (Semantics o) => a -> Form -> o -> Bool
  reachesOn plan f start = start |= reaches plan f

instance IsPlan OfflinePlan where
  reaches []          goal = goal
  reaches (step:rest) goal = Conj [step, PubAnnounce step (reaches rest goal)]

offlineSearch :: (Eq a, Semantics a, Update a Form) =>
   Int ->    -- maximum number of actions
   a ->      -- the starting model or structure
   [Form] -> -- the available actions
   [Form] -> -- intermediate goals / safety formulas
   Form ->   -- the goal formula (when to stop)
   [OfflinePlan]
offlineSearch roundsLeft now acts safety goal
  | now |= goal = [ [] ] -- done, goal reached
  | roundsLeft == 0 = [    ] -- give up
  | otherwise = [ a : rest
                | a <- acts
                , now |= a              -- only allow truthful announcements!
                , let new = now `update` a  -- the new state
                , new /= now                -- ignore useless actions
                , all (new |=) safety
                -- depth-first search:
                , rest <- offlineSearch (roundsLeft-1) new acts safety goal ]

data Plan a = Stop
            | Do String a (Plan a)
            | Check Form (Plan a)
            | IfThenElse Form (Plan a) (Plan a)
  deriving (Eq,Ord,Show)

execute :: Update state a => Plan a -> state -> Maybe state
execute Stop                 s = Just s
execute (Do _ action rest)   s | s |= preOf action = execute rest (s `update` action)
                               | otherwise         = Nothing
execute (Check f rest)       s = if s |= f then execute rest s else Nothing
execute (IfThenElse f pa pb) s = if s |= f then execute pa   s else execute pb s

instance IsPlan (Plan Form) where
  reaches Stop goal = goal
  reaches (Do _ toBeAn next) goal = Conj [toBeAn, PubAnnounce toBeAn (reaches next goal)]
  reaches (Check toBeChecked next) goal = Conj [toBeChecked, reaches next goal]
  reaches (IfThenElse condition planA planB) goal =
    Conj [ condition `Impl` reaches planA goal, Neg condition `Impl` reaches planB goal ]

instance IsPlan (Plan Sym.MultipointedEvent) where
  reaches Stop goal = goal
  reaches (Do actLabel action next) goal = dix (Dyn actLabel (toDyn action)) (reaches next goal)
  reaches (Check toBeChecked next) goal = Conj [toBeChecked, reaches next goal]
  reaches (IfThenElse check planA planB) goal =
    Conj [ check `Impl` reaches planA goal, Neg check `Impl` reaches planB goal ]

dix :: DynamicOp -> Form -> Form
dix op f = Conj [Dia op Top, box op f]

data Task state action = Task state [(String,action)] Form
  deriving (Eq,Ord,Show)

findPlan :: (Eq state, Update state action) => Int -> Task state action -> [Plan action]
findPlan d (Task now acts goal)
  | now |= goal = [ Stop ]
  | d == 0      = [      ]
  | otherwise   = [ Do lbl act continue
                  | (lbl,act) <- acts
                  , isTrue now (preOf act)
                  , now /= update now act -- ignore useless actions
                  , continue <- findPlan (d-1) (Task (update now act) acts goal) ]

class Eq o => HasPerspective o where
  asSeenBy :: o -> Agent -> o
  isLocalFor :: o -> Agent -> Bool
  isLocalFor state i = state `asSeenBy` i == state

instance HasPerspective Exp.MultipointedModelS5 where
  asSeenBy (m@(Exp.KrMS5 _ rel _), actualWorlds) agent = (m, seenWorlds) where
    seenWorlds = sort $ concat $ filter (not . null . intersect actualWorlds) (apply rel agent)

instance HasPerspective ExpK.MultipointedModel where
  asSeenBy (ExpK.KrM m, actualWorlds) agent = (ExpK.KrM m, seenWorlds) where
    seenWorlds = sort $ nub $ M.foldlWithKey
      (\ vs w (_,rel) -> vs ++ concat [ rel M.! agent | w `elem` actualWorlds ])
      []
      m

instance HasPerspective Sym.MultipointedKnowScene where
  asSeenBy (Sym.KnS props lawbdd obs, statesBdd) agent =
    (Sym.KnS props lawbdd obs, seenStatesBdd) where
      seenStatesBdd = existsSet otherps statesBdd
      otherps = map fromEnum (props \\ apply obs agent)

flipRelBdd :: [Prp] -> SymK.RelBDD -> SymK.RelBDD
flipRelBdd props = fmap $ Sym.relabelWith [(SymK.mvP p, SymK.cpP p) | p <- props ]

instance HasPerspective SymK.MultipointedBelScene where
  asSeenBy (SymK.BlS props lawbdd obsBdds, statesBdd) agent =
    (SymK.BlS props lawbdd obsBdds, seenStatesBdd) where
      flippedObsBdd = flipRelBdd props (obsBdds M.! agent)
      seenStatesBdd = SymK.unmvBdd $ existsSet (map fromEnum $ SymK.cp props) <$>
                        (con <$> SymK.cpBdd statesBdd <*> flippedObsBdd)

data CoopTask state action = CoopTask state [Owned action] Form
  deriving (Eq,Ord,Show)

instance (HasPerspective state, Eq action) => HasPerspective (CoopTask state action) where
  asSeenBy (CoopTask start acts goal) agent = CoopTask (start `asSeenBy` agent) acts goal

type Labelled a = (String,a)

type Owned action = (Agent,Labelled action)

type ICPlan action = [Owned action]
-- note: there is no check that the action is actually local for the agent!

ppICPlan :: ICPlan action -> String
ppICPlan [] = ""
ppICPlan [(agent,(label,_))] = agent ++ ":" ++ label ++ "."
ppICPlan ((agent,(label,_)):rest) = agent ++ ":" ++ label ++ "; " ++ ppICPlan rest

icSolves :: (Typeable action, Semantics state) => ICPlan action -> CoopTask state action -> Bool
icSolves plan (CoopTask start acts goal) =
  all ((`elem` map fst acts) . fst) plan && start |= icSuccForm plan goal

icSuccForm :: Typeable a => [(Agent, (String, a))] -> Form -> Form
icSuccForm [] goal = goal
icSuccForm ((agent,(label,action)):rest) goal =
  K agent (dix (Dyn label (toDyn action)) (icSuccForm rest goal))

findSequentialIcPlan :: (Typeable action, Eq state, Update state action) => Int -> CoopTask state action -> [ICPlan action]
findSequentialIcPlan d (CoopTask now acts goal)
  | now |= goal = [ [] ] -- goal reached
  | d == 0      = [    ] -- give up
  | otherwise   = [ (agent,(label, act)) : continue
                  | a@(agent,(label,act)) <- acts
                  , now |= preOf act           -- action must be executable
                  , now |= K agent (preOf act) -- agent must know that it is executable!
                  , now /= update now act      -- ignore useless actions
                  , continue <- findSequentialIcPlan (d-1) (CoopTask (update now act) acts goal) -- DFS!
                  , (a:continue) `icSolves` CoopTask now acts goal  ]

findSequentialIcPlanBFS :: (Typeable action, Eq state, Update state action) => Int -> CoopTask state action -> Maybe (ICPlan action)
findSequentialIcPlanBFS maxDepth (CoopTask start acts goal) = loop [([],start)] where
  loop [] = Nothing
  loop ((done,now):rest)
    | now |= goal = Just done -- FIXME: need stronger condition >> icSolves (CoopTask now acts goal) (done)
    | otherwise   = loop $ rest ++
                      [ (done ++ [a], update now act) -- TODO optimize (vocabOf start) ?
                      | length done < maxDepth     -- do not use more than maxDepth actions
                      , a@(agent,(_,act)) <- acts
                      , now |= preOf act           -- action must be executable
                      , now |= K agent (preOf act) -- agent must know that it is executable!
                      , now /= update now act      -- ignore useless actions
                      ]
