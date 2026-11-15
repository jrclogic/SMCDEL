{-# LANGUAGE TupleSections #-}

{- |

__Converting between S5 Kripke Models and Knowledge Structures__

We define and implement translation methods
between the Kripke models and action models from "SMCDEL.Explicit.S5"
and the knowledge structures and transformers from "SMCDEL.Symbolic.S5".
This allows us to switch between explicit and symbolic model checking.

Reference:

- [MG2018]
  Malvin Gattinger (2018):
  /New Directions in Model Checking Dynamic Epistemic Logic./
  PhD thesis, ILLC, Amsterdam.
  <https://malv.in/phdthesis>

-}

module SMCDEL.Translations.S5 where

import Data.Containers.ListUtils (nubOrd)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (groupBy,sort,(\\),elemIndex,intersect)
import Data.Maybe (listToMaybe,fromJust)

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Explicit.S5
import SMCDEL.Internal.Help (anydiffWith,alldiff,alleqWith,apply,powerset,(!),seteq,subseteq)
import SMCDEL.Other.BDD2Form

-- * Tools for Equivalence

-- | A function mapping worlds to states.
type StateMap = World -> State

{- |
Given
a pointed S5 Kripke model \(\mathcal{M} = (W,\pi,{\cal K}_1,\dots,{\cal K}_n), w)\)
with vocabulary \(U \subseteq V\),
a scene $(\mathcal{F} = (V,\theta, O_1,\dots, O_n)$ with actual state $s$,
and
a function \(g \colon W \rightarrow \mathcal{P}(V)\),
check whether $g$ maps worlds of \(\mathcal{M}\) to __equivalent__ states of $\mathcal{F}$
by checking the following conditions:

- C1: For all \(w_1, w_2 \in W\) and all \(i\) such that \(1 \leq i \leq n\),
  we have that \(g(w_1) \cap O_i = g(w_2) \cap O_i\) iff \(w_1 {\cal K}_i w_2\);
- C2: For all \(w \in W\) and \(p \in U\),
  we have that \(p\in g(w)\) iff \(\pi(w)(p) = \top\);
- C3: For every \(s\subseteq V\),
  \(s\) is a state of \(\mathcal{F}\) iff \(s=g(w)\) for some \(w \in W\); and
- \(g(w) = s\).

Then for any \(\mathcal{L}(U)\)-formula \(\varphi\) we have:
  \[ (\mathcal{F},g(w)) \vDash \varphi \iff (\mathcal{M},w) \vDash \varphi \]
See Lemma 2.4.1 in [MG2018] for the proof.
-}
equivalentWith :: PointedModelS5 -> KnowScene -> StateMap -> Bool
equivalentWith (m@(KrMS5 ws rel val), actw) (kns@(KnS _ _ obs), curs) g =
  c1 && c2 && c3 && g actw == curs where
    c1 = all (\l -> knsLink l == kriLink l) linkSet where
      linkSet = [ (i,w1,w2) | w1 <- ws, w2 <- ws, w1 <= w2, i <- map fst rel ]
      knsLink (i,w1,w2) = let oi = obs ! i in (g w1 `intersect` oi) `seteq` (g w2 `intersect` oi)
      kriLink (i,w1,w2) = any (\p -> w1 `elem` p && w2 `elem` p) (rel ! i)
    c2 = and [ (p `elem` g w) == ((val ! w) ! p) | w <- ws, p <- vocabOf m ]
    c3 = statesOf kns `seteq` nubOrd (map g ws)

{-|
Given a pointed model and a KnowScene,
try to /find/ a function \(g\) linking them and showing their equivalence.
A fully naive approach would be to consider all possible maps from worlds to subsets of \(U\),
but we already know by C2 that we need \(\{ p \mid \pi(w)(p) = \top \} \subseteq g(w)\).
Hence we only generate all possible choices for the propositions
in the vocabulary of the knowledge structure but not the Kripke Model.
Finally, we filter out the good maps using `equivalentWith`
and connect the given actual world and state.
-}
findStateMap :: PointedModelS5 -> KnowScene -> Maybe StateMap
findStateMap pm@(KrMS5 _ _ val, w) scn@(kns, s)
  | vocabOf pm `subseteq` vocabOf kns = listToMaybe goodMaps
  | otherwise = error "vocabOf pm not subseteq vocabOf kns"
  where
    extraProps = vocabOf kns \\ vocabOf pm
    allFuncs :: Eq a => [a] -> [b] -> [a -> b]
    allFuncs []     _  = [ const undefined ]
    allFuncs (x:xs) ys = [ \a -> if a == x then y else f a | y <- ys, f <- allFuncs xs ys ]
    allMaps, goodMaps :: [StateMap]
    baseMap  = map fst . filter snd . (val !)
    allMaps  = [ \v -> baseMap v ++ restf v | restf <- allFuncs (worldsOf pm) (powerset extraProps) ]
    goodMaps = filter (\g -> g w == s && equivalentWith pm scn g) allMaps

-- * Knowledge Structures to S5 Kripke Models

{-|
Given a knowledge structure \(\mathcal{F} = (V, \theta, O_1, \dots, O_n)\) and actual state \(s\),
define the Kripke model \({\cal M}(\mathcal{F} ) := (W, \pi , {\cal K}_1 , \dots, {\cal K}_n )\)
where

- \(W\) is the set of all states of \(\mathcal{F}\) given by `statesOf`,
- for each \(w \in W\), let the assignment \(\pi (w)\) be \(w\) itself and
- for each agent \(i\) and all \(v,w \in W\), let \(v {\cal K}_i w\) iff \(v \cap O_i = w \cap O_i\).

Then for any \(\varphi\) we have:
  \[ (\mathcal{F},s) \vDash \varphi \iff (M(\mathcal{F}),s) \vDash \varphi\ \]

This is function \(\mathcal{M}(\cdot)\) from Definition 2.4.2 and Theorem 2.4.3 in [MG2018].
-}
knsToKripke :: KnowScene -> PointedModelS5
knsToKripke (kns, curState) = (m, curWorld) where
  (m@(KrMS5 worlds _ _), g) = knsToKripkeWithG kns
  curWorld = case [ w | w <- worlds, g w == curState ] of
    [cW] -> cW
    _    -> error "knsToKripke failed: Invalid current state."

-- | Like `knsToKripke` but also return the function \(g\).
knsToKripkeWithG :: KnowStruct -> (KripkeModelS5, StateMap)
knsToKripkeWithG kns@(KnS ps _ obs) =
  (KrMS5 worlds rel val, g) where
    g w    = statesOf kns !! w
    lav    = zip (statesOf kns) [0..(length (statesOf kns)-1)]
    val    = map ( \(s,n) -> (n,state2kripkeass s) ) lav where
      state2kripkeass s = map (\p -> (p, p `elem` s)) ps
    rel    = [(i,rfor i) | i <- map fst obs]
    rfor i = map (map snd) (groupBy ( \ (x,_) (y,_) -> x==y ) (sort pairs)) where
      pairs = map (\s -> (s `intersect` (obs ! i), lav ! s)) (statesOf kns)
    worlds = map snd lav

-- | Like `knsToKripke` but for multipointed structures.
knsToKripkeMulti :: MultipointedKnowScene -> MultipointedModelS5
knsToKripkeMulti (kns,statesBdd) = (m, ws) where
  (m, g) = knsToKripkeWithG kns
  ws = filter (\w -> evaluateFun statesBdd (\k -> P k `elem` g w)) (worldsOf m)

-- *  S5 Kripke Models to Knowledge Structures

{- |
Given an S5 model \({\cal M}=(W,\pi,{\cal K}_1,\dots,{\cal K}_n)\) with vocabulary \(U\),
define an equivalent knowledge structure \(\mathcal{F}(\mathcal{M})\) as follows.
For each agent \(i\),
  write \(\gamma_{i,1},\dots,\gamma_{i,k_i}\) for the equivalence classes given by \({\cal K}_i\) and
  let \(l_i:= \mathsf{ceiling}(\log_2 k_i)\).
  Let \(O_i\) be a set of \(l_i\) many fresh propositions.
  This yields the sets of observational variables \(O_1,\dots,O_n\), all disjoint to each other.
  If agent \(i\) has a total relation, i.e.\ only one equivalence class, then we have \(O_i=\varnothing\).
  Enumerate \(k_i\) many subsets of \(O_i\) as \(O_{\gamma_{i,1}},\dots,O_{\gamma_{i,k_i}}\)
  and define \(g_i : W \rightarrow \mathcal{P}(O_i)\) by
  \(g_i(w):= O_{\gamma_i(w)}\) where \(\gamma_i(w)\) is the \({\cal K}_i\)-equivalence class of \(w\).
Let \(V := U \cup \bigcup_{0<i\leq n}O_i\) and define \(g \colon W \rightarrow \mathcal{P}(V)\) by
  \[ g(w):=\{ v \in U \mid \pi(w)(v)=\top \}\cup \bigcup_{0<i\leq n}g_i(w) \]
Finally, let \(\mathcal{F}({\cal M}) :=(V,\theta_M,O_1,\dots,O_n)\) using
  \[ \theta_M := \bigvee \left \{ g(w) \sqsubseteq V \mid w\in W \right \} \]
where \(\sqsubseteq\) is the abbreviation from `booloutofForm`.

Then for any formula \(\varphi\) we have:
  \[ (\mathcal{M},w) \vDash \varphi \iff (\mathcal{F}({\cal M}),g(w))\vDash \varphi \]
-}
kripkeToKns :: PointedModelS5 -> KnowScene
kripkeToKns (m, curWorld) = (kns, curState) where
    (kns, g)  = kripkeToKnsWithG m
    curState  = sort $ g curWorld

-- | Same as `kripkeToKns` but also return \(g\).
kripkeToKnsWithG :: KripkeModelS5 -> (KnowStruct, StateMap)
kripkeToKnsWithG m@(KrMS5 worlds rel val) = (KnS ps law obs, g) where
  v         = vocabOf m
  ags       = map fst rel
  newpstart = fromEnum $ freshp v -- start counting new propositions here
  amount i  = ceiling (logBase 2 (fromIntegral $ length (rel ! i)) :: Float) -- = |O_i|
  newpstep  = maximum [ amount i | i <- ags ]
  newps i   = map (\k -> P (newpstart + (newpstep * inum) +k)) [0..(amount i - 1)] -- O_i
    where inum = fromJust $ elemIndex i (map fst rel)
  copyrel i = zip (rel ! i) (powerset (newps i)) -- label equiv.classes with P(O_i)
  gag i w   = snd $ head $ filter (\(ws,_) -> w `elem` ws) (copyrel i)
  g w       = filter (apply (val ! w)) v ++ concat [ gag i w | i <- ags ]
  ps        = v ++ concat [ newps i | i <- ags ]
  law       = disSet [ booloutof (g w) ps | w <- worlds ]
  obs       = [ (i,newps i) | i<- ags ]

-- | Convert a multipointed S5 Kripke model to a knoweldge structure.
-- See also `smartKripkeToKns`.
kripkeToKnsMulti :: MultipointedModelS5 -> MultipointedKnowScene
kripkeToKnsMulti (model, curWorlds) = (kns, curStatesLaw) where
  (kns, g) = kripkeToKnsWithG model
  curStatesLaw = disSet [ booloutof (g w) (vocabOf kns) | w <- curWorlds ]

-- | Check if all worlds in a model have pairwise different valuations.
uniqueVals :: KripkeModelS5 -> Bool
uniqueVals (KrMS5 _ _ val) = alldiff (map snd val)

-- | Get lists of variables which agent i does (not) observe in model m.
-- Note: does /not/ preserve all information and thus
-- does not characterize every possible S5 relation.
obsnobs :: KripkeModelS5 -> Agent -> ([Prp],[Prp])
obsnobs m@(KrMS5 _ rel val) i = (obs,nobs) where
  propsets = map (map (map fst . filter snd . apply val)) (apply rel i)
  obs = filter (\p -> all (alleqWith (elem p)) propsets) (vocabOf m)
  nobs = filter (\p -> any (anydiffWith (elem p)) propsets) (vocabOf m)

-- | Test if all relations can be described using observariables.
descableRels :: KripkeModelS5 -> Bool
descableRels m@(KrMS5 ws rel val) = all (descable . fst) rel where
  wpairs = [ (v,w) | v <- ws, w <- ws ]
  descable i = cover && correct where
    (obs,nobs) = obsnobs m i
    cover = sort (vocabOf m) == sort (obs ++ nobs) -- implies disjointness
    correct = all (\pair -> oldrel pair == newrel pair) wpairs
    oldrel (v,w) = v `elem` head (filter (elem w) (apply rel i))
    newrel (v,w) = (factsAt v `intersect` obs) == (factsAt w `intersect` obs)
    factsAt w = map fst $ filter snd $ apply val w

-- | Try to find an equivalent knowledge structure without adding fresh atomic propositions.
-- Will use `smartKripkeToKnsWithoutChecks` when valuations are unique and relations can be
-- described using observariables. Otherwise falls back to using `kripkeToKnsMulti`.
smartKripkeToKns :: PointedModelS5 -> KnowScene
smartKripkeToKns (m, cur) =
  if uniqueVals m && descableRels m
    then smartKripkeToKnsWithoutChecks (m, cur)
    else kripkeToKns (m, cur)

-- | Unsafe version of `smartKripkeToKns`.
smartKripkeToKnsWithoutChecks :: PointedModelS5 -> KnowScene
smartKripkeToKnsWithoutChecks (m@(KrMS5 worlds rel val), cur) =
  (KnS ps law obs, curs) where
    ps = vocabOf m
    g w = filter (apply (apply val w)) ps
    law = disSet [ booloutof (g w) ps | w <- worlds ]
    obs = map (\(i,_) -> (i,obsOf i) ) rel
    obsOf = fst.obsnobs m
    curs = map fst $ filter snd $ apply val cur

-- TODO: test the above on symmetric and random models, how does it perform?

-- * Knowledge Transformers to S5 Action Models

{- |
Given a Knowledge Transformer \(\mathcal{X}=(V^+,\theta^+,O_1^+,\dots,O_n^+)\),
define an S5 action model \(\mathsf{Act}(\mathcal{X})\) as follows.
First, let the set of actions be \(A:= \mathcal{P}(V^+)\).
Second, for any two actions \(\alpha,\beta\in A\),
  let \(\alpha R_i \beta\) iff \(\alpha \cap O_i^+ = \beta \cap O_i^+\).
Third, for any action \(\alpha\), let
  \(\mathsf{pre}(\alpha):= \theta^+\left(\frac{\alpha}\top\right)\left(\frac{V^+ \setminus \alpha}\bot\right)\).
Finally, let \(\mathsf{Act}(\mathcal{X}) := (A,{(R_i)}_{i\in I},\mathsf{pre})\).

Then for all (\mathcal{F},s) we have:
  \[
  (\mathcal{F},s) \times (\mathcal{X},x) \vDash \phi
  \iff
  ({\cal M}(\mathcal{F}) \times \mathsf{Act}(\mathcal{X})) , (s,x) \vDash \phi
  \]

Note: this function can yield action models with contradictions as preconditions.
We do /not/ remove those as it might very well be that a transformar and thus an action model can never be applied.
-}
transformerToActionModelWithG :: KnowTransformer -> (ActionModelS5, StateMap)
transformerToActionModelWithG trf@(KnTrf addprops addlaw changelaw addobs) = (ActMS5 acts actrel, g) where
  actlist = zip (powerset addprops) [0..(2 ^ length addprops - 1)]
  acts    = [ (a, (preFor ps, postsFor ps)) | (ps,a) <- actlist ] where
    preFor ps = simplify $ substitSet (map (, Top) ps ++ map (, Bot) (addprops \\ ps)) addlaw
    postsFor ps =
      [ (q, formOf $ restrictSet (changelaw ! q) [(p, P p `elem` ps) | (P p) <- addprops])
      | q <- map fst changelaw ]
  actrel    = [(i,rFor i) | i <- agentsIn trf] where
    rFor i  = map (map snd) (groupBy ( \ (x,_) (y,_) -> x==y ) (pairs i))
    pairs i = sort $ map (\(set,a) -> (intersect set $ addobs ! i,a))
                         (filter ((`elem` map fst acts) . snd) actlist)
  g :: Action -> State
  g a = head [ x | (x, a') <- actlist, a' == a ]

-- | Use `transformerToActionModelWithG` to translate an event to a pointed action model.
eventToAction :: Event -> PointedActionModelS5
eventToAction (trf, event) = (actm, faction) where
  (actm@(ActMS5 acts _), g) = transformerToActionModelWithG trf
  faction = case [ a | (a,_) <- acts, g a == event ] of
    [fct] -> fct
    _ -> error $ unlines
      [ "Could not find faction:"
      , "  acts = " ++ show acts
      , "  map (g . fst) acts = " ++ show (map (g . fst) acts)
      , "  event = " ++ show event
      , "  trf = " ++ show trf
      ]

-- | Use `transformerToActionModelWithG` to translate an multipointed event to a multipointed action model.
eventToActionMulti :: MultipointedEvent -> MultipointedActionModelS5
eventToActionMulti (trf, actualEventLaw) = (actm, factions) where
  (actm@(ActMS5 acts _), g) = transformerToActionModelWithG trf
  factions = [ a | (a,_) <- acts, bddEval (g a) actualEventLaw ]

-- TODO add tests for the translations of unpointed and multipointed events above!

-- TODO Should "Event" rather be called "Pointed KnowTransformer" ?

-- * S5 Action Models to Knowledge Transformers

{- |
Given an S5 action model \(\mathcal{A}=(A,{(R_i)}_{i\in I},\mathsf{pre})\),
return a transformer as follows and an equivalence map \(g_\mathcal{A}\) from actions to events.
Let \(P\) be a finite set of fresh propositions such that there is an injective labeling function
  \(g_\mathcal{A}: A \to \mathcal{P}(P)\) and let
  \[ \Phi := \bigwedge \left \{ (g_\mathcal{A}(a) \sqsubseteq P) \rightarrow \mathsf{pre}(a) \,\middle|\, a \in A \right \} \]
where \(\sqsubseteq\) is the ``out of'' abbreviation from `booloutofForm`.
Now, for each \(i\):
  Write \(A / R_i\) for the set of equivalence classes induced by \(R_i\).
  Let \(O_i^+\) be a finite set of fresh propositions such that
    there is an injective \(g_i : A/R_i \to \mathcal{P}(O_i^+)\) and let
  \[ \Phi_i := \bigwedge
      \left \{ \left(g_i(\alpha) \sqsubseteq O_i \right) \rightarrow
        \left(\bigvee_{a \in \alpha} (g_\mathcal{A}(a) \sqsubseteq P) \right)
      \,\middle|\, \alpha \in A/R_i \right \} \]
Finally, let
  \(V^+ := P \cup \bigcup_{i\in I} P_i\)
  and \(\theta^+ := \Phi \land \bigwedge_{i\in I} \Phi_i\),
then return
  \(\mathsf{Trf}(\mathcal{A}) := (V^+, \theta^+, O_1^+, \dots, O_n^+)\).

Then for any model \(\mathcal{M}\)
and any formula \(\varphi\) over the
vocabulary of \(\mathcal{M}\) we have
  \[
    \mathcal{M} \times \mathcal{A}, (w,\alpha) \vDash \varphi
    \iff
    \mathcal{F}(\mathcal{M}) \times \mathsf{Trf}(\mathcal{A}), (g_\mathcal{M}(w) \cup g_\mathcal{A}(\alpha))  \vDash \varphi
  \]
where \(g_\mathcal{M}\) is from `kripkeToKnsWithG`.
-}
actionToTransformerWithMap :: ActionModelS5 -> (KnowTransformer, StateMap)
actionToTransformerWithMap (ActMS5 acts actrel) = (KnTrf addprops addlaw changelaw addobs, eventMap) where
  actions = map fst acts
  ags          = map fst actrel
  addprops     = actionprops ++ actrelprops
  (P fstnewp)  = freshp . propsIn $ concat [ pre : concatMap (\(p,f) -> [PrpF p, f]) posts | (_,(pre,posts)) <- acts]  -- avoid props occurring anywhere in the in action model
  actionprops  = [P fstnewp..P maxactprop] -- new props to distinguish all actions
  maxactprop   = fstnewp + ceiling (logBase 2 (fromIntegral $ length actions) :: Float) -1
  actpropsRel  = zip actions (powerset actionprops)
  ell          = apply actpropsRel -- label actions with subsets of actionprops
  happens a    = booloutofForm (ell a) actionprops -- boolean formula to say that a happens
  actform      = Disj [ Conj [ happens a, pre ] | (a,(pre,_)) <- acts ] -- connect new propositions to preconditions
  actrelprops  = concat [ newps i | i <- ags ] -- new props to distinguish actions for i
  actrelpstart = maxactprop + 1
  newps i      = map (\k -> P (actrelpstart + (newpstep * inum) +k)) [0..(amount i - 1)]
    where inum = fromJust $ elemIndex i (map fst actrel)
  amount i     = ceiling (logBase 2 (fromIntegral $ length (apply actrel i)) :: Float)
  newpstep     = maximum [ amount i | i <- ags ]
  copyactrel i = zip (apply actrel i) (powerset (newps i)) -- label equclasses-of-actions with subsets-of-newps
  actrelfs i   = [ Equi (booloutofForm (apply (copyactrel i) as) (newps i)) (Disj (map happens as)) | as <- apply actrel i ]
  actrelforms  = concatMap actrelfs ags
  factsFor a i = snd $ head $ filter (\(as,_) -> a `elem` as) (copyactrel i)
  eventMap a   = ell a ++ concatMap (factsFor a) ags
  addlaw       = simplify $ Conj (actform : actrelforms)
  changeprops  = sort $ nubOrd $ concatMap (\(_,(_,posts)) -> map fst posts) acts -- propositions to be changed
  changelaw    = [ (p, changeFor p) | p <- changeprops ] -- encode postconditions
  changeFor p  = disSet [ boolBddOf $ Conj [ happens a, safepost posts p ] | (a,(_,posts)) <- acts ]
  addobs       = [ (i,newps i) | i<- ags ]

-- | Use `actionToTransformerWithMap` to translate a pointed action model to an event.
actionToEvent :: PointedActionModelS5 -> Event
actionToEvent (actm, action) = (trf, efacts) where
  (trf, g) = actionToTransformerWithMap actm
  efacts = g action

-- | Use `actionToTransformerWithMap` to translate a multipointed action model to a multipointed event.
actionToEventMulti :: MultipointedActionModelS5 -> MultipointedEvent
actionToEventMulti (actm, curActions) = (trf, curActionsLaw) where
  (trf@(KnTrf addprops _ _ _), g) = actionToTransformerWithMap actm
  curActionsLaw = disSet [ booloutof (g w) addprops | w <- curActions ]
