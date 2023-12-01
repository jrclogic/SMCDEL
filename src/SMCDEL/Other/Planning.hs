{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

{- |
Here we provide some wrapper functions for epistemic planning via model checking.
Our main inspiration for this are the following references.

- [LPW 2011]
  Benedikt Löwe, Eric Pacuit, and Andreas Witzel (2011):
  /DEL Planning and Some Tractable Cases/.
  LORI 2011.
  <https://doi.org/10.1007/978-3-642-24130-7_13>
- [EBMN 2017]
  Thorsten Engesser, Thomas Bolander, Robert Mattmüller, and Bernhard Nebel (2017):
  /Cooperative Epistemic Multi-Agent Planning for Implicit Coordination/.
  Ninth Workshop on Methods for Modalities.
  <https://doi.org/10.4204/EPTCS.243.6>

/NOTE/: This module is still experimental and under development.
-}

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

-- * Generic Planning functions and type classes

class IsPlan a where
  -- | A formula saying that the given plan reaches the given goal.
  reaches :: a -> Form -> Form
  reachesOn :: (Semantics o) => a -> Form -> o -> Bool
  reachesOn plan f start = start |= reaches plan f

-- * Sequential Plans with Public Announcements

{- $
We first consider /sequential/ plans which are list of formulas to be publicly and truthfully announced, one after each other.
These are also called /offline/ plans.
We write \(\sigma\) for any sqeuential plan and \(\epsilon\) for the empty plan which does nothing.
The following then defines a formula which says that the given plan reaches a given goal \(\gamma\):

\[
\begin{array}{ll}
\mathsf{reaches}(\epsilon)(\gamma) & := & \gamma \\
\mathsf{reaches}(\phi;\sigma)(\gamma) & := & \langle \phi \rangle (\mathsf{reaches}(\sigma)(\gamma))
\end{array}
\]

-}

-- | A list of announcements to be made.
type OfflinePlan = [Form]

instance IsPlan OfflinePlan where
  reaches []          goal = goal
  reaches (step:rest) goal = Conj [step, PubAnnounce step (reaches rest goal)]

-- | Depth-first search for sequential public announcement plans.
offlineSearch :: (Eq a, Semantics a, Update a Form) =>
   Int ->    -- ^ maximum number of actions
   a ->      -- ^ starting model or structure
   [Form] -> -- ^ available actions (as public announcements)
   [Form] -> -- ^ intermediate goals / safety formulas
   Form ->   -- ^ goal
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

-- * Policy Plans with General Actions

{- $
A /policy/, also called /online plan/ can include tests and choices, to decide which action to do depending on the results of previous announcements.
To represent such plans we use a tree where non-terminal nodes are actions to be done or formulas to be checked.
Each action node has one outgoing edge and each checking node has two outgoing edges, leading to the follow-up plans.
Terminal-nodes are stop signals.

In contrast to the previous section we now also allow more general actions, namely any type in the `Update` class, for example action models and transformers.
-}

-- | A plan with choice, i.e. a policy.
data Plan a = Stop -- ^ Stop.
            | Do String a (Plan a) -- ^ Do a given action.
            | Check Form (Plan a) -- ^ Check that a formula holds. (If not, fail.)
            | IfThenElse Form (Plan a) (Plan a) -- ^ If ... then ... else ... .
  deriving (Eq,Ord,Show)

-- | Try to execute a policy plan on a given state.
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

-- | The \(((\alpha))\phi := \langle \alpha \rangle \land [\alpha] \phi\) abbreviation from [EBMN 2017].
-- We call it `dix` because it is a combination of /di/amond and bo/x/.
dix :: DynamicOp -> Form -> Form
dix op f = Conj [Dia op Top, box op f]


-- * Planning Tasks

{- $
A planning task (also called a planning problem) is given by a start, a list of actions and a goal.
Note that \texttt{state} and \texttt{action} here are type variables,
  because we use polymorphic functions for explicit and symbolic planning in K and S5.
-}

data Task state action = Task state [(String,action)] Form
  deriving (Eq,Ord,Show)


-- Given a maximal search depth and a task, we search for a plan as follows.
findPlan :: (Eq state, Update state action) => Int -> Task state action -> [Plan action]
findPlan d (Task now acts goal)
  | now |= goal = [ Stop ]
  | d == 0      = [      ]
  | otherwise   = [ Do lbl act continue
                  | (lbl,act) <- acts
                  , isTrue now (preOf act)
                  , now /= update now act -- ignore useless actions
                  , continue <- findPlan (d-1) (Task (update now act) acts goal) ]

-- * Perspective Shifts

class Eq o => HasPerspective o where
  asSeenBy :: o -> Agent -> o
  isLocalFor :: o -> Agent -> Bool
  isLocalFor state i = state `asSeenBy` i == state

-- ** Perspective Shits in S5

-- $
-- Given a multipointed S5 model \((\M,s)\), the local state of an agent \(i\) is given by
-- \[ s^i := \{ w \in W \mid \exists v \in s : v \sim_i w \} \]
-- This is the definition given in [EBMN 2017] and implemented by `asSeenBy`.

-- | See ...
instance HasPerspective Exp.MultipointedModelS5 where
  asSeenBy (m@(Exp.KrMS5 _ rel _), actualWorlds) agent = (m, seenWorlds) where
    seenWorlds = sort $ concat $ filter (not . null . intersect actualWorlds) (apply rel agent)

-- | Here we also implement perspective shifts in K.
-- The authors of [EBMN 2017] only consider S5.
-- Given a multipointed Kripke model $(\M,s)$, let the local state of $i$ be:
-- \[ s^i := \{ w \in W \mid \exists v \in s : v R_i w \} \]
-- Intuitively, these are all worlds the agent considers possible if the current state is $s$.
instance HasPerspective ExpK.MultipointedModel where
  asSeenBy (ExpK.KrM m, actualWorlds) agent = (ExpK.KrM m, seenWorlds) where
    seenWorlds = sort $ nub $ M.foldlWithKey
      (\ vs w (_,rel) -> vs ++ concat [ rel M.! agent | w `elem` actualWorlds ])
      []
      m

-- | We can also make perspective shifts symbolically.
-- In the S5 setting we can exploit symmetry as follows.
-- Suppose we have a multipointed scene $(\F,\sigma)$ where $\sigma \in \Lng_B(V)$ encodes the set of actual states.
-- As usual, we assume that agent $i$ has the observational variables $O_i$.
-- Then the perspective of $i$ is given by:
-- \[ \sigma^i :=  \exists (V \setminus O_i) \sigma \]
-- On purpose we do not use $\theta$ in order to avoid redundancy in the resulting multipointed scene.
instance HasPerspective Sym.MultipointedKnowScene where
  asSeenBy (Sym.KnS props lawbdd obs, statesBdd) agent =
    (Sym.KnS props lawbdd obs, seenStatesBdd) where
      seenStatesBdd = existsSet otherps statesBdd
      otherps = map fromEnum (props \\ apply obs agent)

-- ** Perspective Shits in K

{- $
Note that in S5 we always have \(s \subseteq s^i\), but this is not the case in general for K.
Also note that \((\cdot)^i\) is no longer idempotent if \(R_i\) is not transitive.

For the K setting we first need a way to flip the direction of the encoded relation \(\Omega_i\).
This is done by `fliRelBdd`.

Suppose we have a set of actual states encoded by \(\sigma \in \mathcal{L}_B(V)\).
Then the perspective of agent \(i\) is given by:

\[ \sigma^i := \exists V' (\Omega_i^\smile \land \sigma') \]

The following chain of equivalences shows that this definition does indeed what we want.
A state \(s\) satisifes the encoding of the local state \(\sigma^i\) iff it can be reached from a state \(t\) which satisfies the encoding of the global state \(\sigma\).

\[ \begin{array}{rl}
     & s \vDash \sigma^i \\
\iff & s \vDash \exists V' (\Omega_i^\smile \land \sigma') \\
\iff & \exists t \subseteq V : s \cup t' \vDash (\Omega_i^\smile \land \sigma') \\
\iff & \exists t \subseteq V : t \cup s' \vDash (\Omega_i        \land \sigma ) \\
\iff & \exists t \subseteq V : t \vDash \sigma \text{ and } t \cup s' \vDash \Omega_i
\end{array} \]

Again we do not include \(\theta\) here to avoid redundancy in the multipointed structure.

-}
-- TODO If not transitive, does it make sense to consider "what would my perspective be?"
-- TODO For KD45 we still have the following properties: ...

-- TODO instance HasPerspective Sym.MultipointedEvent

-- | Simultaneously prime and unprime all its variables. (TODO: \subst)
-- Formally, the resulting BDD is \( \Omega_i^\smile := \subst{V \cup V'}{V' \cup V} \Omega_i \).
flipRelBdd :: [Prp] -> SymK.RelBDD -> SymK.RelBDD
flipRelBdd props = fmap $ Sym.relabelWith [(SymK.mvP p, SymK.cpP p) | p <- props ]

-- | See ...
instance HasPerspective SymK.MultipointedBelScene where
  asSeenBy (SymK.BlS props lawbdd obsBdds, statesBdd) agent =
    (SymK.BlS props lawbdd obsBdds, seenStatesBdd) where
      flippedObsBdd = flipRelBdd props (obsBdds M.! agent)
      seenStatesBdd = SymK.unmvBdd $ existsSet (map fromEnum $ SymK.cp props) <$>
                        (con <$> SymK.cpBdd statesBdd <*> flippedObsBdd)

-- TODO instance HasPerspective SymK.MultipointedEvent

-- * Implicit Cooperation

-- $ We now introduce owner functions as discussed in [EBMN 2017] and based on [LPW 2011]

data CoopTask state action = CoopTask state [Owned action] Form
  deriving (Eq,Ord,Show)

instance (HasPerspective state, Eq action) => HasPerspective (CoopTask state action) where
  asSeenBy (CoopTask start acts goal) agent = CoopTask (start `asSeenBy` agent) acts goal


-- ** Implicitly coordinated sequential plans

-- $ As done in section 3.2 of [EBMN 2017].

-- | Helper type to label actions with strings.
type Labelled a = (String,a)

-- | An owned action is a pair of an agent and a labelled action.
type Owned action = (Agent,Labelled action)

-- | An implicitly coordinated plan is a sequence of owned actions.
-- Note: there is no check that the action is actually local for the agent!
type ICPlan action = [Owned action]

instance Typeable a => IsPlan (ICPlan a) where
  -- | A formula to say that the given IC plan reaches the given foal.
  reaches [] goal = goal
  reaches ((agent,(label,action)):rest) goal =
    K agent (dix (Dyn label (toDyn action)) (reaches rest goal))

-- | Pretty print an IC plan.
ppICPlan :: ICPlan action -> String
ppICPlan [] = ""
ppICPlan [(agent,(label,_))] = agent ++ ":" ++ label ++ "."
ppICPlan ((agent,(label,_)):rest) = agent ++ ":" ++ label ++ "; " ++ ppICPlan rest

-- | Check that the given IC plan solves the given Coop task.
icSolves :: (Typeable action, Semantics state) => ICPlan action -> CoopTask state action -> Bool
icSolves plan (CoopTask start acts goal) =
  all ((`elem` map fst acts) . fst) plan && reachesOn plan goal start

-- | Depth-first search for sequential IC plans.
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

-- | Breadth-first search for shortest IC plans.
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

-- TODO
-- - [x] DFS with max depth
-- - [x] BFS
-- - conditional plans
-- - random CoopTask generation
-- - testing
-- - plan visualisation?
-- - MCTS
