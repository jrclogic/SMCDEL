{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, ScopedTypeVariables #-}

{- |
This module defines the standard semantics of Dynamic Epistemic Logic ($\mathsf{S5}_n$) on Kripke models.
The result is a simple explicit model checker, similar to "SMCDEL.Explicit.DEMO_S5" from [vE2014].
The module here is also used for the translations given in "SMCDEL.Translations.S5".

References used here:

- [BMS1998]
  Alexandru Baltag, Lawrence S. Moss, Slawomir Solecki (1998):
  /The logic of public announcements, common knowledge, and private suspicions./
  TARK VII.
  <http://www.tark.org/proceedings/tark_jul22_98/p43-baltag.pdf>

- [vE2014]
  Jan van Eijck (2014):
  /DEMO-S5./
  <https://staff.fnwi.uva.nl/d.j.n.vaneijck2/software/demo_s5/>

-}

module SMCDEL.Explicit.S5 where

import Control.Arrow (second,(&&&))
import Data.Typeable (cast)
import Data.GraphViz
import Data.List
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)

import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Internal.Help (alleqWith,fusion,intersection,apply,(!),lfp)
import Test.QuickCheck

-- * Kripke Models

{- $

A /Kripke model/ for a set of agents \(I=\{1,\dots,n\}\) is a tuple
\({\cal M}=(W,\pi ,{\cal K}_1 ,\dots,{\cal K}_n )\), where \(W\) is a set of
/worlds/, \(\pi\) associates with each world a truth assignment to
the primitive propositions, so that \(\pi (w)(p)\in \{ \top, \bot \}\)
for each world \(w\) and primitive proposition \(p\), and
\({\cal K}_1,\dots, {\cal K}_n\) are binary accessibility relations on \(W\).
By convention, \(W^{\cal M}\), \({\cal K}_i^{\cal M}\) and \(\pi^{\cal M}\) are used to refer to the components of \(\cal M\).
We omit the superscript \(\cal M\) if it is clear from context.
Finally, let \({\cal C}_\Delta^{\cal M}\) be the transitive closure of \(\bigcup_{i\in\Delta}{\cal K}_i^{\cal M}\).

A /pointed Kripke model/ is a pair \(({\cal M},w)\) consisting of a Kripke model and a world \(w \in W^{\cal M}\).
A model \(\cal M\) is called an /S5 Kripke model/ iff, for every \(i\), \({\cal K}_i^{\cal M}\) is an equivalence relation.

In the module here we only implement S5 models. For the more general models, use "SMCDEL.Explicit.K" instead.

A model \(\cal M\) is called /finite/ iff \(W^{\cal M}\) is finite.
In the implementation here we always assume finite models, even if Haskell due to its laziness in principle would be able to work with infinite lists of worlds.
-}

-- | Possible worlds are represented by integers.
type World = Int

class HasWorlds a where
  worldsOf :: a -> [World]

instance (HasWorlds a, Pointed a b) => HasWorlds (a,b) where worldsOf = worldsOf . fst

-- | A partition to encode an equivalence relation.
type Partition = [[World]]

-- | An assignment, given explicitly by listing the truth value for each atomic proposition.
type Assignment = [(Prp,Bool)]

-- | S5 Kripke Model.
data KripkeModelS5 = KrMS5 [World]               -- ^ set of worlds
                           [(Agent,Partition)]   -- ^ epistemic relations
                           [(World,Assignment)]  -- ^ valuation function
                      deriving (Eq,Ord,Show)

instance Pointed KripkeModelS5 World
type PointedModelS5 = (KripkeModelS5,World)

instance DefaultPoint KripkeModelS5 World where
  pointDef m = case worldsOf m of
    [] -> error "Given KripkeModelS5 has no worlds."
    (w : _) -> (m, w)

instance Pointed KripkeModelS5 [World]
type MultipointedModelS5 = (KripkeModelS5,[World])

instance ToMulti PointedModelS5 MultipointedModelS5 where
  toMulti (m, w) = (m, [w])

instance DefaultPoint KripkeModelS5 [World] where
  pointDef kns = toMulti (pointDef kns :: PointedModelS5)

instance HasAgents KripkeModelS5 where
  agentsOf (KrMS5 _ rel _) = map fst rel

instance HasVocab KripkeModelS5 where
  vocabOf (KrMS5 _ _ []) = error "empty valuation function"
  vocabOf (KrMS5 _ _ ((_,v):_)) = map fst v

instance HasWorlds KripkeModelS5 where
  worldsOf (KrMS5 ws _ _) = ws

newtype PropList = PropList [Prp]

withoutWorld :: KripkeModelS5 -> World -> KripkeModelS5
withoutWorld (KrMS5 worlds parts val) w = KrMS5
  (delete w worlds)
  (map (second (filter (/=[]) . map (delete w))) parts)
  (filter ((/=w).fst) val)

withoutProps :: KripkeModelS5 -> [Prp] -> KripkeModelS5
withoutProps (KrMS5 worlds parts val) dropProps = KrMS5
  worlds
  parts
  (map (second $ filter ((`notElem` dropProps) . fst)) val)

instance Arbitrary PropList where
  arbitrary = do
    moreprops <- sublistOf (map P [1..10])
    return $ PropList $ P 0 : moreprops

randomPartFor :: [World] -> Gen Partition
randomPartFor worlds = do
  indices <- infiniteListOf $ choose (1, length worlds)
  let pairs = zip worlds indices
  let parts = [ sort $ map fst $ filter ((==k).snd) pairs | k <- [1 .. (length worlds)] ]
  return $ sort $ filter (/=[]) parts

instance Arbitrary KripkeModelS5 where
  arbitrary = do
    nonActualWorlds <- sublistOf [1..8]
    let worlds = 0 : nonActualWorlds
    val <- mapM (\w -> do
      myAssignment <- zip defaultVocabulary <$> infiniteListOf (choose (True,False))
      return (w,myAssignment)
      ) worlds
    parts <- mapM (\i -> do
      myPartition <- randomPartFor worlds
      return (i,myPartition)
      ) defaultAgents
    return $ KrMS5 worlds parts val
  shrink m@(KrMS5 worlds _ _) =
    [ m `withoutWorld` w | w <- worlds, not (null $ delete w worlds) ]

-- | Standard semantics for explicit model checking on S5 Kripke models.
-- See Definition 1.1.3 and 1.2.2 in [MG2018].
eval :: PointedModelS5 -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (KrMS5 _ _ val, cur) (PrpF p) = apply (apply val cur) p
eval pm (Neg form)    = not $ eval pm form
eval pm (Conj forms)  = all (eval pm) forms
eval pm (Disj forms)  = any (eval pm) forms
eval pm (Xor  forms)  = odd $ length (filter id $ map (eval pm) forms)
eval pm (Impl f g)    = not (eval pm f) || eval pm g
eval pm (Equi f g)    = eval pm f == eval pm g
eval pm (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (m@(KrMS5 _ rel _),w) (K ag form) = all (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrMS5 _ rel _),w) (Kw ag form) = alleqWith (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrMS5 _ rel _),w) (Ck ags form) = all (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) ckrel
  ckrel = fusion $ concat [ apply rel i | i <- ags ]
eval (m@(KrMS5 _ rel _),w) (Ckw ags form) = alleqWith (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) ckrel
  ckrel = fusion $ concat [ apply rel i | i <- ags ]
eval (m@(KrMS5 worlds rel _),w) (Dk ags form) = all (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) dkrel
  dkrel = intersection worlds [ apply rel i | i <- ags ]
eval (m@(KrMS5 worlds rel _),w) (Dkw ags form) = alleqWith (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) dkrel
  dkrel = intersection worlds [ apply rel i | i <- ags ]
eval (m@(KrMS5 worlds _ _),_) (G form) = all (\w' -> eval (m,w') form) worlds
eval pm (PubAnnounce form1 form2) =
  not (eval pm form1) || eval (update pm form1) form2
eval pm (Dia (Dyn dynLabel d) f) =
  eval pm (preOf d) && case cast d of
    Just (pactm :: PointedActionModelS5) -> eval (pm `update` pactm) f
    Nothing -> case cast d of
      Just (mpactm :: MultipointedActionModelS5) -> eval (pm `update` mpactm) f
      Nothing -> error $ "cannot update S5 Kripke model with '" ++ dynLabel ++ "':\n  " ++ show d

-- | Is the given formula valid in the model, i.e. true at all worlds?
valid :: KripkeModelS5 -> Form -> Bool
valid m@(KrMS5 worlds _ _) f = all (\w -> eval (m,w) f) worlds

instance Semantics KripkeModelS5 where
  isTrue m f = all (\w -> isTrue (m,w) f) (worldsOf m)

instance Semantics PointedModelS5 where
  isTrue = eval

instance Semantics MultipointedModelS5 where
  isTrue (m,ws) f = all (\w -> isTrue (m,w) f) ws

-- | Public announcements on Kripke models.
instance Update KripkeModelS5 Form where
  -- | No checks, to announce formulas not globally true.
  checks = []
  unsafeUpdate m@(KrMS5 sts rel val) form = KrMS5 newsts newrel newval where
    newsts = filter (\s -> eval (m,s) form) sts
    newrel = map (second relfil) rel
    relfil = filter ([]/=) . map (filter (`elem` newsts))
    newval = filter (\p -> fst p `elem` newsts) val

instance Update PointedModelS5 Form where
  unsafeUpdate (m,w) f = (unsafeUpdate m f, w)

instance Update MultipointedModelS5 Form where
  unsafeUpdate (m,ws) f =
    let newm = unsafeUpdate m f in (newm, ws `intersect` worldsOf newm)

-- * Visualisation

-- $
-- We visualize models using "SMCDEL.Internal.TexDisplay".
-- For example output, see "SMCDEL.Examples"

instance KripkeLike KripkeModelS5 where
  directed = const False
  getNodes (KrMS5 ws _ val) = map (show &&& labelOf) ws where
    labelOf w = tex $ apply val w
  getEdges (KrMS5 _ rel _) =
    nub [ (a,show x,show y) | a <- map fst rel, part <- apply rel a, x <- part, y <- part, x < y ]

instance TexAble KripkeModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, cur) = [show cur]

instance TexAble PointedModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, curs) = map show curs

instance TexAble MultipointedModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

-- * Bisimulations

type Bisimulation = [(World,World)]

checkBisim :: Bisimulation -> KripkeModelS5 -> KripkeModelS5 -> Bool
checkBisim [] _                   _                     = False
checkBisim z  m1@(KrMS5 _ rel1 val1) m2@(KrMS5 _ rel2 val2) =
  all (\(w1,w2) ->
        (val1 ! w1 == val2 ! w2)  -- same valuation
    && and [ any (any (\v2 -> (v1,v2) `elem` z)) (filter (elem w2) (rel2 ! ag)) -- forth
           | ag <- agentsOf m1, v1 <- concat $ filter (elem w1) (rel1 ! ag) ]
    && and [ any (any (\v1 -> (v1,v2) `elem` z)) (filter (elem w1) (rel1 ! ag)) -- back
           | ag <- agentsOf m2, v2 <- concat $ filter (elem w2) (rel2 ! ag) ]
      ) z

checkBisimPointed :: Bisimulation -> PointedModelS5 -> PointedModelS5 -> Bool
checkBisimPointed z (m1,w1) (m2,w2) = (w1,w2) `elem` z && checkBisim z m1 m2

--  TODO findBisimulationFrom :: PointedModelS5 -> PointedModelS5 -> Maybe Bisimulation

-- * Minimization and Optimization

-- | Generated submodel of a pointed model.
-- This is the smallest submodel closed under the epistemic relations
generatedSubmodel :: PointedModelS5 -> PointedModelS5
generatedSubmodel (KrMS5 oldWorlds rel val, cur) =
  if cur `notElem` oldWorlds
    then error "Actual world is not in the model!"
    else (KrMS5 newWorlds newrel newval, cur) where
      newWorlds :: [World]
      newWorlds = lfp follow [cur] where
        follow xs = sort . nub $ concat [ part | (_,parts) <- rel, part <- parts, any (`elem` part) xs ]
      newrel = map (second $ filter (any (`elem` newWorlds))) rel
      newval = filter (\p -> fst p `elem` newWorlds) val

-- TODO rewrite bisim and generated Submodel to work on multipointed by default

-- | Compute the equivalence classes of bisimilar worlds within a model. Used in `bisiminimize`.
--
-- We use the following version of partition refinement.
-- The initial partition is given by the valuation.
-- Then we `foldl` through all agents once, splitting the existing blocks with their relation.
-- As we only have equivalence relations, one pass is enough and no looping until we reach a fixpoint is needed.
bisimClasses :: KripkeModelS5 -> [[World]]
bisimClasses m@(KrMS5 _ rel val) = refine sameAssignmentPartition where
  sameAssignmentPartition =
    map (map snd)
      $ groupBy (\x y -> fst x == fst y)
        $ sort (map swap val)
  refine parts = sort $ map sort $ foldl splitByAgent parts (agentsOf m)
  splitByAgent parts a =
    concat [ filter (not . null) [ ws `intersect` aPart | aPart <- rel ! a ] | ws <- parts ]

checkBisimClasses :: KripkeModelS5 -> Bool
checkBisimClasses m =
  and [ checkBisimPointed (swapZ w1 w2) (m,w1) (m,w2)
      | part <- bisimClasses m, w1 <- part, w2 <-part, w1 /= w2 ] where
    swapZ w1 w2 = sort $ [(w1,w2),(w2,w1)] ++ [ (w,w) | w <- worldsOf m \\ [w1,w2] ]

-- | Minimize a pointed model under bisimulation.
-- Uses `bisimClasses` to find a possibly smaller model.
bisiminimize :: PointedModelS5 -> PointedModelS5
bisiminimize (m,w) =
  if all ((==1) . length) (bisimClasses m)
    then (m,w) -- nothing to minimize
    else (KrMS5 newWorlds newRel newVal, copyFct w) where
      KrMS5 _ oldRel oldVal = m
      copyRel      = zip (bisimClasses m) [1..]
      copyFct wOld = snd $ head $ filter ((wOld `elem`) . fst) copyRel
      newWorlds    = map snd copyRel
      newRel       = [ (a,newRelFor a) | a <- agentsOf m ]
      newRelFor a  = [ nub [ copyFct wOld | wOld <- part ] |  part <- oldRel ! a ]
      newVal       = [ (wNew, oldVal ! wOld) | (wOld:_,wNew) <- copyRel ]

instance Optimizable PointedModelS5 where
  -- | Optimize a Kripke model by taking the generated submodel and then minimizing under bisimulation.
  -- Does /not/ use the given vocabulary.
  optimize _ = bisiminimize . generatedSubmodel

-- * S5 Action Models

-- $
-- We model epistemic and ontic events using the well-known action models from [BMS1998].

type Action = Int
type PostCondition = [(Prp,Form)]

data ActionModelS5 = ActMS5 [(Action,(Form,PostCondition))] [(Agent,Partition)]
  deriving (Eq,Ord,Show)

instance UsesAgents ActionModelS5 where
  agentsIn (ActMS5 _ rel) = map fst rel

instance UsesVocab ActionModelS5 where
  propsIn (ActMS5 acts _) = nub $ concatMap
    ( \ (_,(pre,posts))
      -> propsIn pre ++ concat [ p : propsIn f | (p,f) <- posts ]
    ) acts
  replPsIn repl (ActMS5 acts rel) = ActMS5
    (map ( \ (a, (pre, posts))
           -> (a, ( replPsIn repl pre
                  , [ (replPsIn repl p, replPsIn repl f) | (p,f) <- posts ]))
         ) acts)
    rel

-- | A safe way to `lookup` all postconditions
safepost :: PostCondition -> Prp -> Form
safepost posts p = fromMaybe (PrpF p) (lookup p posts)

instance Pointed ActionModelS5 Action
type PointedActionModelS5 = (ActionModelS5, Action)

instance HasPrecondition ActionModelS5 where
  preOf _ = Top

instance HasPrecondition PointedActionModelS5 where
  preOf (ActMS5 acts _, actual) = fst (acts ! actual)

instance Pointed ActionModelS5 [Action]
type MultipointedActionModelS5 = (ActionModelS5,[Action])

instance HasPrecondition MultipointedActionModelS5 where
  preOf (am, actuals) = Disj [ preOf (am, a) | a <- actuals ]

instance KripkeLike ActionModelS5 where
  directed = const False
  getNodes (ActMS5 acts _) = map labelOf acts where
    labelOf (a,(pre,posts)) = (show a, concat
      [ "$\\begin{array}{c} ? " , tex pre, "\\\\"
      , intercalate "\\\\" (map showPost posts)
      , "\\end{array}$" ])
    showPost (p,f) = tex p ++ " := " ++ tex f
  getEdges am@(ActMS5 _ rel) =
    nub [ (a, show x, show y) | a <- agentsIn am, part <- rel ! a, x <- part, y <- part, x < y ]
  getActuals _ = [ ]
  nodeAts _ True  = [shape BoxShape, style solid]
  nodeAts _ False = [shape BoxShape, style dashed]

instance TexAble ActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedActionModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, cur) = [show cur]

instance TexAble PointedActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedActionModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, curs) = map show curs

instance TexAble MultipointedActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance Arbitrary ActionModelS5 where
  arbitrary = do
    BF f <- sized $ randomboolformWith [P 0 .. P 4]
    BF g <- sized $ randomboolformWith [P 0 .. P 4]
    BF h <- sized $ randomboolformWith [P 0 .. P 4]
    myPost <- (\_ -> do
      proptochange <- elements [P 0 .. P 4]
      postconcon <- elements $ [Top,Bot] ++ map PrpF [P 0 .. P 4]
      return [ (proptochange, postconcon) ]
      ) (0::Action)
    return $
      ActMS5
        [ (0,(Top,[]))
        , (1,(f  ,[]))
        , (2,(g  ,myPost))
        , (3,(h  ,[]))     ]
        ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3::Int]]) | k<-[1..5::Int] ])

instance DynOp ActionModelS5

instance Update KripkeModelS5 ActionModelS5 where
  checks = [haveSameAgents]
  unsafeUpdate m am@(ActMS5 acts _) =
    let (newModel,_) = unsafeUpdate (m, worldsOf m) (am, map fst acts) in newModel

instance DynOp PointedActionModelS5

instance Update PointedModelS5 PointedActionModelS5 where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) (actm, a) = head <$> unsafeUpdate (m, [w]) (actm, [a])

instance DynOp MultipointedActionModelS5

instance Update PointedModelS5 MultipointedActionModelS5 where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) mpactm = head <$> unsafeUpdate (m, [w]) mpactm

instance Update MultipointedModelS5 PointedActionModelS5 where
  checks = [haveSameAgents] -- do not check precondition!
  unsafeUpdate mpm (actm, a) = unsafeUpdate mpm (actm, [a])

instance Update MultipointedModelS5 MultipointedActionModelS5 where
  checks = [haveSameAgents] -- do not check precondition!
  unsafeUpdate (m@(KrMS5 oldWorlds oldrel oldval), oldcurs) (ActMS5 acts actrel, factions) =
    (KrMS5 newWorlds newrel newval, newcurs) where
      startcount        = maximum oldWorlds + 1
      copiesOf (s,a)    = [ (s, a, a * startcount + s) | eval (m, s) (fst $ acts ! a) ]
      newWorldsTriples  = concat [ copiesOf (s,a) | s <- oldWorlds, (a,_) <- acts ]
      newWorlds         = map (\(_,_,x) -> x) newWorldsTriples
      newval            = map (\(s,a,t) -> (t, newValAt (s,a))) newWorldsTriples where
        newValAt sa = [ (p, newValAtFor sa p) | p <- vocabOf m ]
        newValAtFor (s,a) p = case lookup p (snd (acts ! a)) of
          Just postOfP -> eval (m, s) postOfP
          Nothing      -> (oldval ! s) ! p
      listFor ag        = cartProd (apply oldrel ag) (apply actrel ag)
      newPartsFor ag    = [ cartProd as bs | (as,bs) <- listFor ag ]
      translSingle pair = filter (`elem` newWorlds) $ map (\(_,_,x) -> x) $ copiesOf pair
      transEqClass      = concatMap translSingle
      nTransPartsFor ag = filter (/= []) $ map transEqClass (newPartsFor ag)
      newrel            = [ (a, nTransPartsFor a)  | a <- map fst oldrel ]
      newcurs           = concat [ map (\(_,_,x) -> x) $ copiesOf (s,a) | s <- oldcurs, a <- factions ]
      cartProd xs ys    = [ (x,y) | x <- xs, y <- ys ]

-- * Frequently-used Action Models

-- | Public announcement as an action model.
pubAnnounceAction :: [Agent] -> Form -> PointedActionModelS5
pubAnnounceAction ags f = (ActMS5 [(0,(f,[]))] [ (i,[[0]]) | i <- ags ], 0)

-- | Semi-private group announcement as an action model.
groupAnnounceAction :: [Agent] -> [Agent] -> Form -> PointedActionModelS5
groupAnnounceAction everyone listeners f = (am, 1) where
  am = ActMS5
    [ (1, (f, [])), (2, (Neg f, [])) ]
    [ (i, if i `elem` listeners then [[1],[2]] else [[1,2]] ) | i <- everyone ]
