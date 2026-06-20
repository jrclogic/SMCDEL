{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

{- |

The implementation in "SMCDEL.Symbolic.S5" only works for models where the
epistemic accessibility relation is an equivalence relation.
This is because only those can be described by sets of observational variables.
In fact, not even every S5 relation on distinctly valuated worlds can be modeled with observational variables --- this is why our translation procedure in "SMCDEL.Translation.S5" has to add additional atomic propositions.

To overcome this limitation, here we generalize the definition of knowledge structures.
Using well-known methods from temporal model checking, arbitrary relations can also be represented as BDDs.
See for example [GR2002].
Remember that in a knowledge structure we can identify states with boolean assignments and those are just sets of propositions.
Hence a relation on states with unique valuations can be seen as a relation between sets of propositions.
We can therefore represent it with the BDD of a characteristic function on a double vocabulary,
as described in Section 5.2 of [CGP1999].

Intuitively, we construct (the BDD of) a formula which is true exactly for the pairs of boolean assignments that are connected by the relation.

Our symbolic model checker can then also be used for non-S5 models.

For further explanations, see Sections 2.6 to 2.8 of [MG2018].

References:

- [CGP1999]
  E.M. Clarke, O. Grumberg and D.A. Peled (1999):
  /Model Checking/.
  MIT Press, ISBN 9780262032704.

- [GR2002]
  Nikos Gorogiannis and Mark D. Ryan (2002):
  /Implementation of Belief Change Operators Using BDDs/
  Studia Logica, volume 70, number 1, pages 131-156.
  <https://doi.org/10.1023/A:1014610426691>

- [MG2018]
  Malvin Gattinger (2018):
  /New Directions in Model Checking Dynamic Epistemic Logic./
  PhD thesis, ILLC, Amsterdam.
  <https://malv.in/phdthesis>

-}

module SMCDEL.Symbolic.K where

import Data.Tagged

import Control.Arrow ((&&&),first)
import Data.Dynamic (fromDynamic)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (delete,intercalate,sort,intersect,nub,(\\))
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Test.QuickCheck

import SMCDEL.Explicit.K
import SMCDEL.Internal.Help (apply,lfp,powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.S5 (State,texBDD,boolBddOf,booloutof,texBddWith,bddEval,relabelWith)

-- * Type-safe BDDs for Relations

{- $

To encode relations with BDDs we use the following method, well-known from temporal model checking.
Remember that in a knowledge structure we can identify states with boolean assignments.
Furthermore, if we fix a global set of variables, those are just sets of propositions.
Hence @Rel State = [(State,State)] = [([Prp],[Prp])]@,
i.e. a relation over states is in fact a relation on sets of propositions.
We can therefore represent a relation with the BDD of a characteristic function on a double vocabulary, as described in Section 5.2 of [CGP1999].
Intuitively, we construct (the BDD of) a formula which is true exactly for the pairs of boolean assignments that are connected by the relation.

To do so, we consider a doubled vocabulary.
For example, \(( \{p,p_3\}, \{p_2\} ) \in R\) should be represented by the fact that the assignment \(\{p,p_3,p_2'\}\) satisfies the formula representing \(R\).

Informally we can just write \(p'\) instead of \(p\) and \(p_2'\) instead of \(p_2\) and so on, but in the implementation more work is needed.
In particular we have to choose an ordering of all variables in the double vocabulary.
The two candidates are interleaving order or stacking all primed variables above/below all unprimed ones.

We choose the interleaving order because it has two advantages:
(i) Relations in epistemic models are often already decided by a difference in one specific propositional variable.
Hence \(p\) and \(p'\) should be close to each other to keep the BDD small.
(ii) Using infinite lists we can write general functions to go back and forth between the vocabularies.
Notably, these functions are independent of how many variables we will actually use.

+----------+-------------------+-------------------+
| Variable | Single vocabulary | Double vocabulary |
+==========+===================+===================+
| \(p   \) | @P 0@             | @P 0@             |
+----------+-------------------+-------------------+
| \(p'  \) |                   | @P 1@             |
+----------+-------------------+-------------------+
| \(p_1 \) | @P 1@             | @P 2@             |
+----------+-------------------+-------------------+
| \(p_1'\) |                   | @P 3@             |
+----------+-------------------+-------------------+
| \(p_2 \) | @P 2@             | @P 4@             |
+----------+-------------------+-------------------+
| \(p_2'\) |                   | @P 5@             |
+----------+-------------------+-------------------+

To switch between the normal and the double vocabulary, we use the helper
functions `mv`, `cp` and their inverses.

>            ----mv-->
>    p in V             p in V u V'
>            <--unmv--
>    |   ^
>    |   |
>   cp  uncp
>    |   |
>    v   |
>
>  p' in V u V'

-}

-- | Map \(p\) in the single vocabulary to \(p\) in the double vocabulary.
mvP :: Prp -> Prp
mvP (P n) = P  (2*n)

-- | Map \(p\) in the single vocabulary to \(p'\) in the double vocabulary.
cpP :: Prp -> Prp
cpP (P n) = P ((2*n) + 1) -- represent p' in the double vocabulary

-- | Map \(p\) or \(p'\) in double vocabulary to \(p\) in the single vocabulary.
unmvcpP :: Prp -> Prp
unmvcpP (P m) | even m    = P $ m `div` 2
              | otherwise = P $ (m-1) `div` 2

mv, cp :: [Prp] -> [Prp]
mv = map mvP
cp = map cpP

unmv, uncp :: [Prp] -> [Prp]
-- | Go from p in double vocabulary to p in single vocabulary.
unmv = map f where
  f (P m) | odd m    = error "unmv failed: Number is odd!"
          | otherwise = P $ m `div` 2
-- | Go from p' in double vocabulary to p in single vocabulary.
uncp = map f where
  f (P m) | even m    = error "uncp failed: Number is even!"
          | otherwise = P $ (m-1) `div` 2

-- ** BDDs for Relations

{- $

The following type `RelBDD` is in fact just a newtype of `Bdd`.
Tags (aka labels) from the module Data.Tagged can be used to distinguish
objects of the same type which should not be combined or mixed.
Making these differences explicit at the type level can rule out certain
mistakes already at compile time which otherwise might only be discovered
at run time or not at all.

The use case here is to distinguish BDDs for formulas over different
vocabularies, i.e.~sets of atomic propositions.
For example, the BDD of \(p_1\) in the standard vocabulary \(V\) uses the variable
\(1\), but in the vocabulary of \(V \cup V'\) the proposition \(p_1\) is mapped to
variable \(3\) while \(p_1'\) is mapped to \(4\).
This is implemented in the mv and cp functions above which we are now going to
lift to BDDs.

If `RelBDD` and `Bdd` were synonyms (as it was the case in a previous version of
this file) then it would be up to us to ensure that BDDs meant for different
vocabularies would not be combined.
Taking the conjunction of the BDD of \(p\) in \(V\) and the BDD of \(p_2\) in
\(V \cup V'\) just makes no sense — one BDD first needs to be translated to the
vocabulary of the other — but as long as the types match Haskell would
happily generate the chaotic conjunction.

To catch these problems at compile time we now distinguish `Bdd` and `RelBDD`.
In principle this could be done with a simple newtype, but looking ahead we
will need even more different vocabularies (for factual change and symbolic
bisimulations).
It would become tedious to write the same instances of `Functor`,
`Applicative` and `Monad` each time we add a new vocabulary.
Fortunately, "Data.Tagged" already provides us with an instance of
`Functor` for @Tagged t@ for any type @t@.

Also note that `Dubbel` is a unit type, isomorphic to @()@.

-}

data Dubbel
type RelBDD = Tagged Dubbel Bdd

totalRelBdd, emptyRelBdd :: RelBDD
totalRelBdd = pure $ boolBddOf Top
emptyRelBdd = pure $ boolBddOf Bot

allsamebdd :: [Prp] -> RelBDD
allsamebdd ps = pure $ conSet [boolBddOf $ PrpF p `Equi` PrpF p' | (p,p') <- zip (mv ps) (cp ps)]

class TagBdd a where
  tagBddEval :: [Prp] -> Tagged a Bdd -> Bool
  tagBddEval truths querybdd = evaluateFun (untag querybdd) (\n -> P n `elem` truths)

instance TagBdd Dubbel

{- $

Now that `Tagged Dubbel` is an applicative functor, we can lift all the
`Bdd` functions to `RelBDD` using standard notation.
Instead of
  @con (var 1) (var 3) :: RelBDD@
we will now write
  @con <\$> (pure \$ var 1) <*> (pure \$ var 3)@.

On the other hand, something like
  @con <\$> (var 1) <*> (pure \$ var 3)@
would fail and will prevent us from accidentaly mixing up BDDs in different
vocabularies.

-}

-- | Relabels a BDD to represent the formula with primed propositions in the double vocabulary.
-- The type also reflects this change.
cpBdd :: Bdd -> RelBDD
cpBdd b = Tagged $ relabelFun (\n -> (2*n) + 1) b

-- | Relabel a BDD to use the unprimed atoms in in the double vocabulary.
mvBdd :: Bdd -> RelBDD
mvBdd b = Tagged $ relabelFun (2 *) b

-- | Translate a BDD using only unprimed propositions from the double vocabulary to the same formula in the single vocabulary.
-- Will return an error if the given BDD contains odd variables.
unmvBdd :: RelBDD -> Bdd
unmvBdd (Tagged b) =
  relabelFun (\n -> if even n then n `div` 2 else error ("Not even: " ++ show n ++ "in the RelBDD " ++ show b)) b

{- $

The double vocabulary is thus obtained as follows:

>>> mv [(P 0)..(P 3)]
[P 0,P 2,P 4,P 6]

>>> cp [(P 0)..(P 3)]
[P 1,P 3,P 5,P 7]

-}

-- | Encode a relation \(R\) between sets of propositions as a BDD:
-- \[ \mathsf{Bdd}(R) := \bigvee_{(s,t)\in R} \left( ( s \sqsubseteq \mathsf{V} ) \land ( t \sqsubseteq \mathsf{V} )' \right) \]
-- where \((\phi)'\) denotes the formula obtained by priming all propositions in \(\phi\).
--
-- Many operations and tests on relations can be done directly on their BDDs,
-- see page 62 of [MG2018].
propRel2bdd :: [Prp] -> M.Map State [State] -> RelBDD
propRel2bdd props relation = pure $ disSet (M.elems $ M.mapWithKey linkbdd relation) where
  linkbdd here theres =
    con (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there <- theres ] )

-- | An example relation from page 136 of [GoroRyan02:BelRevBDD].
--
-- >>> samplerel
-- fromList [([],[[],[P 1],[P 2],[P 1,P 2]]),([P 1],[[P 1],[P 1,P 2]]),([P 1,P 2],[[P 1,P 2]]),([P 2],[[P 2],[P 1,P 2]])]
-- >>> SMCDEL.Symbolic.K.propRel2bdd [P 1, P 2] SMCDEL.Symbolic.K.samplerel
-- Tagged (ifthenelse (var 2) (ifthenelse (var 3) (ifthenelse (var 4) (var 5) top) bot) (ifthenelse (var 4) (var 5) top))
--
samplerel ::  M.Map State [State]
samplerel = M.fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]


-- * Encoding Kripke Models with BDDs

{- $
We now want to use BDDs to represent the relations of multiple agents
in a general Kripke Model. Suppose we have a model for the vocabulary
\(V\) in which the valuation function assigns to every state a distinct
set of true propositions. To simplify the notation we also write \(s\)
for the set of propositions true at \(s\).

We use an interleaving variable order, i.e. \(p_1,p_1',p_2,p_2',\dots,p_n,p_n'\).
This way a BDD will consider differences in the valuation per proposition and
be more compact if we have observational-variable-like situations.
-}

-- | Translate an agent's relation of worlds to a relation of sets of propositions.
-- The given model must have distinct valuations.
relBddOfIn :: Agent -> KripkeModel -> RelBDD
relBddOfIn i (KrM m)
  | not (distinctVal (KrM m)) = error "m does not have distinct valuations."
  | otherwise = pure $ disSet (M.elems $ M.map linkbdd m) where
    linkbdd (mapPropBool,mapAgentReach)  =
      con
        (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there<-theres ] )
      where
        props = M.keys mapPropBool
        here = M.keys (M.filter id mapPropBool)
        theres = map (truthsInAt (KrM m)) (mapAgentReach ! i)

-- * Belief Structures

-- | A belief structure \( \mathcal{F} = (V, \theta, \Omega_i)\).
data BelStruct = BlS [Prp]                -- ^ vocabulary
                     Bdd                  -- ^ state law
                     (M.Map Agent RelBDD) -- ^ observation laws
                  deriving (Eq,Show)


-- | A belief scene is a belief structure paired with one actual state.
type BelScene = (BelStruct,State)
instance Pointed BelStruct State

-- | A multipointed belief scene is a belief structure paired with multiple actual state encoded as a BDD.
type MultipointedBelScene = (BelStruct,Bdd)
instance Pointed BelStruct Bdd

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ obdds) = M.keys obdds

-- ** Boolean Equivalents

{- $

We use the following notations for boolean assignments and formulas.

- Suppose \(s\) is a boolean assignment and \(\phi\) is a boolean formula in the vocabulary of \(s\).
  Then we write \(s \vDash \phi\) to say that \(s\) makes \(\phi\) true.
- If \(s\) is an assignment for a given vocabulary, we write \(s'\) for the same assignment for a primed copy of the vocabulary.
  For example, take \(\{p_1,p_3\}\) as an assignment over \(V = \{p_1,p_2,p_3,p_4\}\), hence \(\{p_1,p_3\}' = \{p_1',p_3'\}\) is an assignment over \(\{p_1',p_2',p_3',p_4'\}\).
- If \(\phi\) is a boolean formula, write \((\phi)'\) for the result of priming all propositions in \(\phi\).
  For example, \((p_1 \rightarrow (p_3 \land \lnot p_2))' = (p_1' \rightarrow (p_3' \land \lnot p_2')) \).
- If \(s\) and \(t\) are boolean assignments for distinct vocabularies and \(\phi\) is a vocabulary in the combined vocabulary, we write \((st) \vDash \phi\) to say that \(s \cup t\) makes \(\phi\) true.

-}

-- | Given a formula \(\phi\), compute the BDD of \( {\| \phi \|}_\mathcal{F} \),
-- i.e. the Boolean equivalent of the formula, on a given belief structure.
--
-- The interesting case here is
-- \( \|K_i \phi\|_\mathcal{F} := \forall V' ( \theta' \rightarrow ( \Omega_i \rightarrow (|| \phi ||_\mathcal{F})' ) ) \)
--
-- The translation is correct (Theorem 2.6.4 from [MG2018]):
-- \( \mathcal{F},s \vDash \phi \iff s \vDash \|\phi\|_\mathcal{F} \).
bddOf :: BelStruct -> Form -> Bdd
bddOf _   Top           = top
bddOf _   Bot           = bot
bddOf _   (PrpF (P n))  = var n
bddOf bls (Neg form)    = neg $ bddOf bls form
bddOf bls (Conj forms)  = conSet $ map (bddOf bls) forms
bddOf bls (Disj forms)  = disSet $ map (bddOf bls) forms
bddOf bls (Xor  forms)  = xorSet $ map (bddOf bls) forms
bddOf bls (Impl f g)    = imp (bddOf bls f) (bddOf bls g)
bddOf bls (Equi f g)    = equ (bddOf bls f) (bddOf bls g)
bddOf bls (Forall ps f) = forallSet (map fromEnum ps) (bddOf bls f)
bddOf bls (Exists ps f) = existsSet (map fromEnum ps) (bddOf bls f)

-- The interesting case for the K modality:
bddOf bls@(BlS allprops lawbdd obdds) (K i form) = unmvBdd result where
  result = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls form)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

-- Knowing whether is just the disjunction of knowing that and knowing that not.
bddOf bls@(BlS allprops lawbdd obdds) (Kw i form) = unmvBdd result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls f)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

-- Group knowledge/belief notions:
bddOf bls@(BlS voc lawbdd obdds) (Ck ags form) = lfp lambda top where
  ps' = map fromEnum $ cp voc
  lambda :: Bdd -> Bdd
  lambda z = unmvBdd $
    forallSet ps' <$>
      (imp <$> cpBdd lawbdd <*>
        ((imp . disSet <$> sequence [obdds ! i | i <- ags]) <*>
          cpBdd (con (bddOf bls form) z)))
bddOf bls (Ckw ags form) = dis (bddOf bls (Ck ags form)) (bddOf bls (Ck ags (Neg form)))
bddOf bls@(BlS allprops lawbdd obdds) (Dk ags form) = unmvBdd result where
  result = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls form)))
  ps'    = map fromEnum $ cp allprops
  omegai = Tagged $ foldr (con . untag) top [obdds ! i | i <- ags]
bddOf bls@(BlS allprops lawbdd obdds) (Dkw ags form) = unmvBdd result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls f)))
  ps'    = map fromEnum $ cp allprops
  omegai = Tagged $ foldr (con . untag) top [obdds ! i | i <- ags]

-- Global modality:
bddOf bls@(BlS allprops lawbdd _) (G form) =
  forallSet (map (\(P n) -> n) allprops) (imp lawbdd (bddOf bls form))

-- Public announcements only restrict the lawbdd:
bddOf bls (PubAnnounce f g) =
  imp (bddOf bls f) (bddOf (bls `update` f) g)

-- Dynamic operators:
bddOf bls (Dia (Dyn dynLabel d) f) =
    con (bddOf bls preCon)                    -- 5. Prefix with "precon AND ..." (diamond!)
    . relabelWith copyrelInverse              -- 4. Copy back changeProps V_-^o to V_-
    . simulateActualEvents                    -- 3. Simulate actual event(s) [see below]
    . substitSimul [ (k, changeLaw ! p)       -- 2. Replace changeProps V_- with postcons
                   | p@(P k) <- changeProps]  --    (no "relabelWith copyrel", undone in 4)
    . bddOf (bls `unsafeUpdate` trf)          -- 1. boolean equivalent wrt new struct
    $ f
  where
    changeProps = M.keys changeLaw
    copychangeProps = [(freshp $ vocabOf bls ++ addProps)..]
    copyrelInverse  = zip copychangeProps changeProps
    (trf@(Trf addProps addLaw changeLaw _), shiftrel) = shiftPrepare bls trfUnshifted
    (preCon,trfUnshifted,simulateActualEvents) =
      case fromDynamic d of
        -- 3. For a single pointed event, simulate actual event x outof V+
        Just ((t,x) :: Event) -> ( preOf (t,x), t, (`restrictSet` actualAss) )
          where actualAss = [(newK, P k `elem` x) | (P k, P newK) <- shiftrel]
        Nothing -> case fromDynamic d of
          -- 3. For a multipointed event, simulate a set of actual events by ...
          Just ((t,xsBdd) :: MultipointedEvent) ->
              ( preOf (t,xsBdd), t
              , existsSet (map fromEnum addProps)  -- ... replacing addProps with assigments
                . con actualsBdd                   -- ... that satisfy actualsBdd
                . con (bddOf bls addLaw)           -- ... and a precondition.
              ) where actualsBdd = relabelWith shiftrel xsBdd
          Nothing -> error $ "cannot update belief structure with '" ++ dynLabel ++ "':\n  " ++ show d

-- ** Semantics

-- | A formula \(\phi\) is valid on a knowledge structures iff it is true at all states.
-- This is equivalent to the condition that the boolean equivalent formula \({\| \phi \|}_\mathcal{F}\) is true at all states of \(\mathcal{F}\).
-- Furthermore, this is equivalent to saying that the law \(\theta\) of \(\mathcal{F}\) implies \({\| \phi \|}_\mathcal{F}\).
-- Hence, checking for validity can be done by checking if the BDD of \(\theta \rightarrow {\| \phi \|}_\mathcal{F}\) is equivalent (and thus identical) to the \(\top\) BDD.
validViaBdd :: BelStruct -> Form -> Bool
validViaBdd bls@(BlS _ lawbdd _) f = top == imp lawbdd (bddOf bls f)

-- | Check if a formula \(\phi\) is true at a given state \(s\) of a knowledge structure \(\mathcal{F}\).
-- Will compute the boolean equivalent \( {\| \phi \|}_\mathcal{F} \) and check if \(s\) satisfies this BDD.
--
-- Fails with an error in case the BDD is not decided by the given assignment.
-- This usually indicates that the given formula uses propositional variables outside the vocabulary of the given structure.
evalViaBdd :: BelScene -> Form -> Bool
evalViaBdd (bls@(BlS allprops _ _),s) f = let
    bdd  = bddOf bls f
    b    = restrictSet bdd list
    list = [ (n, P n `elem` s) | (P n) <- allprops ]
  in
    case (b==top,b==bot) of
      (True,_) -> True
      (_,True) -> False
      _        -> error $ "evalViaBdd failed: Composite BDD leftover!\n"
        ++ "  bls:  " ++ show bls ++ "\n"
        ++ "  s:    " ++ show s ++ "\n"
        ++ "  form: " ++ show f ++ "\n"
        ++ "  bdd:  " ++ show bdd ++ "\n"
        ++ "  list: " ++ show list ++ "\n"
        ++ "  b:    " ++ show b ++ "\n"

instance Semantics BelStruct where
  isTrue = validViaBdd

instance Semantics BelScene where
  isTrue = evalViaBdd

instance Semantics MultipointedBelScene where
  isTrue (kns@(BlS _ lawBdd _),statesBdd) f =
    let a = lawBdd `imp` (statesBdd `imp` bddOf kns f)
     in a == top

instance Update BelStruct Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate bls@(BlS props lawbdd obs) psi =
    BlS props (lawbdd `con` bddOf bls psi) obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi,s)

-- | Get all states of a knowledge structure.
statesOf :: BelStruct -> [State]
statesOf (BlS allprops lawbdd _) = map (sort.getTrues) prpsats where
  bddvars = map fromEnum allprops
  bddsats = allSatsWith bddvars lawbdd
  prpsats = map (map (first toEnum)) bddsats
  getTrues = map fst . filter snd

-- ** Visualization

texRelBDD :: RelBDD -> String
texRelBDD (Tagged b) = texBddWith texRelProp b where
  texRelProp n
    | even n    = show (n `div` 2)
    | otherwise = show ((n - 1) `div` 2) ++ "'"

bddprefix, bddsuffix :: String
bddprefix = "\\begin{array}{l} \\scalebox{0.3}{"
bddsuffix = "} \\end{array} \n"

instance TexAble BelStruct where
  tex (BlS props lawbdd obdds) = concat
    [ "  \\ensuremath{ \\left( \n"
    , " V = ", tex props, ", "
    , " \\theta = ", bddprefix, texBDD lawbdd, bddsuffix
    , ", "
    , intercalate ", " obddstrings
    , " \\right) } "
    ] where
        obddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (M.toList obdds)
        bddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble BelScene where
  tex (bls, state) = concat
    [ "  \\ensuremath{ \\left( \n", tex bls, ", ", tex state, " \\right) } " ]

instance TexAble MultipointedBelScene where
  tex (bls, statesBdd) = concat
    [ " \\ensuremath{ \\left( \n"
    , tex bls ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD statesBdd
    , "} \\end{array}\n "
    , " \\right) } " ]

-- ** Minimization and Optimization

-- $ The following functions to further minimize/optimize a belief structure are similar to those for knowledge structures.

-- | Restrict each observational law with the state law.
-- This will not lose any information, and results an equivalent belief structure.
cleanupObsLaw :: BelScene -> BelScene
cleanupObsLaw (BlS vocab law obs, s) = (BlS vocab law (M.map clean obs), s) where
  clean relbdd = restrictLaw <$> relbdd <*> (con <$> cpBdd law <*> mvBdd law)

-- | Atomic propositions determined by the state law.
determinedVocabOf :: BelStruct -> [Prp]
determinedVocabOf strct = filter (\p -> validViaBdd strct (PrpF p) || validViaBdd strct (Neg $ PrpF p)) (vocabOf strct)

-- | Atomic propositions not occurring in the observation laws.
nonobsVocabOf  :: BelStruct -> [Prp]
nonobsVocabOf (BlS vocab _law obs) = filter (`notElem` usedVars) vocab where
  usedVars =
    map unmvcpP
    $ sort
    $ nub
    $ concatMap (map P . Data.HasCacBDD.allVarsOf . untag)
    $ M.elems obs

-- | Remove the given atomic propositions from a belief structure.
withoutProps :: [Prp] -> BelStruct -> BelStruct
withoutProps propsToDel (BlS oldProps oldLawBdd oldObs) =
  BlS
    (oldProps \\ propsToDel)
    (existsSet (map fromEnum propsToDel) oldLawBdd)
    (M.map (fmap $ existsSet (map fromEnum propsToDel)) oldObs)

-- | Given a vocabulary to be kept, find pairs of equivalent atomic propositions such that the first one could be removed.
equivExtraVocabOf :: [Prp] -> BelStruct -> [(Prp,Prp)]
equivExtraVocabOf mainVocab bls =
  [ (p,q) | p <- vocabOf bls \\ mainVocab, q <- vocabOf bls, p > q, validViaBdd bls (PrpF p `Equi` PrpF q) ]

-- | Given a pairs of atomic propositions, remove the first one and replace all its occurrences by the second.
replaceWithIn :: (Prp,Prp) -> BelStruct -> BelStruct
replaceWithIn (p,q) (BlS oldProps oldLaw oldObs) =
  BlS (delete p oldProps) (changeBdd oldLaw) (fmap (fmap changeRelBdd) oldObs) where
  changeBdd    = Data.HasCacBDD.relabel [ (fromEnum p, fromEnum q) ]
  changeRelBdd = Data.HasCacBDD.relabel $ sort [ (fromEnum $ mvP p, fromEnum $ mvP q)
                                               , (fromEnum $ cpP p, fromEnum $ cpP q) ]

-- | Given a vocabulary to be kept, replace all redundant propositions from `equivExtraVocabOf`.
replaceEquivExtra :: [Prp] -> BelStruct -> (BelStruct,[(Prp,Prp)])
replaceEquivExtra mainVocab startBls = lfp step (startBls,[]) where
  step (bls,replRel) = case equivExtraVocabOf mainVocab bls of
               []        -> (bls,replRel)
               ((p,q):_) -> (replaceWithIn (p,q) bls, (p,q):replRel)

-- | Removes `determinedVocabOf` and `nonobsVocabOf`, then applies `replaceEquivExtra`.
instance Optimizable BelStruct where
  optimize myVocab bls = fst $ replaceEquivExtra myVocab $
    withoutProps ((determinedVocabOf bls `intersect` nonobsVocabOf bls) \\ myVocab) bls

instance Optimizable BelScene where
  optimize myVocab (oldBls,oldState) = (newBls,newState) where
    intermediateBls = withoutProps (determinedVocabOf oldBls `intersect` nonobsVocabOf oldBls \\ myVocab) oldBls
    removedProps = vocabOf oldBls \\ vocabOf intermediateBls
    intermediateState = oldState \\ removedProps
    (newBls,replRel) = replaceEquivExtra myVocab intermediateBls
    newState = intermediateState \\ map fst replRel

-- | Removes `determinedVocabOf` and `nonobsVocabOf`, then applies `replaceEquivExtra`.
instance Optimizable MultipointedBelScene where
  optimize myVocab (oldBls,oldStatesBdd) = (newKns,newStatesBdd) where
    intermediateBls = withoutProps ((determinedVocabOf oldBls `intersect` nonobsVocabOf oldBls) \\ myVocab) oldBls
    removedProps = vocabOf oldBls \\ vocabOf intermediateBls
    intermediateStatesBdd = existsSet (map fromEnum removedProps) oldStatesBdd
    (newKns,replRel) = replaceEquivExtra myVocab intermediateBls
    newStatesBdd = Data.HasCacBDD.relabel [ (fromEnum p, fromEnum q) | (p,q) <-replRel ] intermediateStatesBdd

-- ** Random Generation

instance Arbitrary BelStruct where
  arbitrary = do
    numExtraVars <- choose (0,2)
    let myVocabulary = defaultVocabulary ++ take numExtraVars [freshp defaultVocabulary ..]
    (BF statelaw) <- sized (randomboolformWith myVocabulary) `suchThat` (\(BF bf) -> boolBddOf bf /= bot)
    obs <- mapM (\i -> do
      BF obsLaw <- sized $ randomboolformWith (sort $ mv myVocabulary ++ cp myVocabulary) -- FIXME should rather be a random BDD?
      return (i,pure $ boolBddOf obsLaw)
      ) defaultAgents
    return $ BlS myVocabulary (boolBddOf statelaw) (M.fromList obs)
  shrink bls = [ withoutProps [p] bls | length (vocabOf bls) > 1, p <- vocabOf bls \\ defaultVocabulary ]

-- * Symbolic Bisimulations

{- $

NOTE: This is currently not implemented.

Suppose we have two structures:
  \[ \mathcal{F}_1=(V,\theta,\Omega_1,\dots,\Omega_n) \]
  \[ \mathcal{F}_2=(V,\theta,\Omega_1,\dots,\Omega_n) \]

A boolean formula \(\beta \in \mathcal{L}(V \cup V^\ast)\) where \(V = V_1 \cap V_2\)
is a /symbolic bisimulation/ iff:

- \(\beta \rightarrow \bigwedge_{p \in V} (p \leftrightarrow p^\ast)\)
    is a tautology (i.e. its BDD is equal to \(\top\)),
- Take any states \(s_1\) of \(F_1\) and \(s_2\) of \(F_2\)
          such that \(s_1 \cup (s_2^\ast) \vDash \beta\),
          any agent \(i\) and any state \(t_1\) of \(F_1\)
          such that \(s_1 \cup t_1' \vDash \Omega_1^i\) in \(F_1\).
        Then there is a state \(t_2\) of \(F_2\) such that
          \(t_1 \cup (t_2^\ast) \vDash \beta\) and
          \(s_2 \cup t_2' \vDash \Omega_2^i\) in \(F_2\),
- and vice versa.

Again, this can also be expressed as a boolean formula.
However, we need /four/ copies of variables now.
Note that the standard definition of bisimulation can also be translated to
first order logic with four variables.
In fact, three variables are enough and we could also overwrite \(V\)
instead of using \({V^\ast}'\) but this will not improve performance.

The second condition as a formula:

\[ \forall (V \cup V^\ast) :
    \beta \rightarrow
      \bigwedge_i \left(
        \forall V':
          \Omega^1_i \rightarrow
            \exists {V^\ast}' :
              \beta' \land {(\Omega^2_i)}^\ast
      \right)
\]

-}

-- * Transformers

data Transformer = Trf
  [Prp]                 -- ^ add props
  Form                  -- ^ event law
  (M.Map Prp Bdd)       -- ^ change law
  (M.Map Agent RelBDD)  -- ^ event observations
  deriving (Eq,Show)

-- | Short-hand to define transformers without factual change.
noChange :: ([Prp] -> Form -> M.Map Prp Bdd -> M.Map Agent RelBDD -> Transformer)
          -> [Prp] -> Form                  -> M.Map Agent RelBDD -> Transformer
noChange kntrf addprops addlaw = kntrf addprops addlaw M.empty

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ obdds) = M.keys obdds

instance HasPrecondition Transformer where
  preOf _ = Top

instance Pointed Transformer State
type Event = (Transformer,State)

instance HasPrecondition Event where
  preOf (Trf addprops addlaw _ _, x) = simplify $ substitOutOf x addprops addlaw

instance Pointed Transformer Bdd
type MultipointedEvent = (Transformer,Bdd)

instance HasPrecondition MultipointedEvent where
  preOf (Trf addprops addlaw _ _, xsBdd) =
    simplify $ Exists addprops (Conj [ formOf xsBdd, addlaw ])

-- ** Visualisation

instance TexAble Transformer where
  tex (Trf addprops addlaw changelaw eventObs) = concat
    [ " \\ensuremath{ \\left( \n"
    , " V^+ = ", tex addprops, ", "
    , " \\theta^+ = ", tex addlaw, ", "
    , tex changeprops, ", "
    , intercalate ", " $ map snd . M.toList $ M.mapWithKey texChange changelaw, ", "
    , intercalate ", " eobddstrings
    , " \\right) } "
    ] where
        changeprops = M.keys changelaw
        texChange prop changebdd = tex prop ++ " := " ++ tex (formOf changebdd)
        eobddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (M.toList eventObs)
        bddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\ensuremath{ \\left( \n", tex trf, ", ", tex eventFacts, " \\right) } " ]

instance TexAble MultipointedEvent where
  tex (trf, eventStates) = concat
    [ " \\ensuremath{ \\left( \n"
    , tex trf ++ ", \\ "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD eventStates
    , "} \\end{array}\n "
    , " \\right) } " ]

-- ** Transformation

-- | Shift addprops to ensure that props and newprops are disjoint.
shiftPrepare :: BelStruct -> Transformer -> (Transformer, [(Prp,Prp)])
shiftPrepare (BlS props _ _) (Trf addprops addlaw changelaw eventObs) =
  (Trf shiftaddprops addlawShifted changelawShifted eventObsShifted, shiftrel) where
    shiftrel = sort $ zip addprops [(freshp props)..]
    shiftaddprops = map snd shiftrel
    -- apply the shifting to addlaw, changelaw and eventObs:
    addlawShifted    = replPsInF shiftrel addlaw
    changelawShifted = M.map (relabelWith shiftrel) changelaw
    -- to shift addObs we need shiftrel in the double vocabulary:
    shiftrelMVCP = sort $ zip (mv addprops) (mv shiftaddprops)
                       ++ zip (cp addprops) (cp shiftaddprops)
    eventObsShifted  = M.map (fmap $ relabelWith shiftrelMVCP) eventObs

instance Update BelScene Event where
  unsafeUpdate (bls@(BlS props law obdds),s) (trf, eventFactsUnshifted) = (BlS newprops newlaw newobs, news) where
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    (Trf addprops addlaw changelaw addObs, shiftrel) = shiftPrepare bls trf
    -- the actual event:
    eventFacts = map (apply shiftrel) eventFactsUnshifted
    -- PART 2: COPYING the modified propositions
    changeprops = M.keys changelaw
    copyrel = zip changeprops [(freshp $ props ++ addprops)..]
    copychangeprops = map snd copyrel
    copyrelMVCP = sort $ zip (mv changeprops) (mv copychangeprops)
                      ++ zip (cp changeprops) (cp copychangeprops)
    -- PART 3: actual transformation
    newprops = sort $ props ++ addprops ++ copychangeprops
    newlaw = conSet $ relabelWith copyrel (con law (bddOf bls addlaw))
                    : [var (fromEnum q) `equ` relabelWith copyrel (changelaw ! q) | q <- changeprops]
    newobs = M.mapWithKey (\i oldobs -> (con . relabelWith copyrelMVCP <$> oldobs) <*> (addObs ! i)) obdds
    news = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , eventFacts
            , filter (\ p -> bddEval (s ++ eventFacts) (changelaw ! p)) changeprops ]

instance Update BelStruct Transformer where
  checks = [haveSameAgents]
  -- | Pointless update of a structure with a transformer, using laziness.
  unsafeUpdate bls ctrf = BlS newprops newlaw newobs where
    (BlS newprops newlaw newobs, _) = unsafeUpdate (bls,undefined::State) (ctrf,undefined::State)

{- $

We also define a multipointed version of this update.
In a `MultipointedEvent` the set of possible events is encoded by a BDD \(\sigma\) over \(V^+\).
An event \(x\) is allowed by \(\sigma\) iff \(x \vDash \sigma\).
Which of the events actually happens is then decided by evaluating the event law:
  \(x\) is possible to happen at \(\mathcal{F},s\) iff
    \(\mathcal{F},s \vDash [x \sqsubseteq V^+] \theta^+\).
Putting both together we get equivalent to the boolean condition
    \(x \vDash \sigma \land [s \sqsubseteq V] \|\theta^+\|_\mathcal{f}\).

To update a belief scene with a multipointed event the event law has to make the events mutually exclusive.
Only then can we return again a belief scene with exactly one actual state.
This is analogous to updating a singlepointed Kripke model with a multi-pointed action model.
Also there the preconditions need to be mutually exclusive to get a single-pointed model again.

-}

instance Update BelScene MultipointedEvent where
  unsafeUpdate (bls,s) (trfUnshifted, eventFactsBddUnshifted) =
    update (bls,s) (trf,selectedEventState) where
      (trf@(Trf addprops addlaw _ _), shiftRel) = shiftPrepare bls trfUnshifted
      eventFactsBdd = relabelWith shiftRel eventFactsBddUnshifted
      selectedEventState :: State
      selectedEventState = map (P . fst) $ filter snd selectedEvent
      selectedEvent = case
                        allSatsWith
                          (map fromEnum addprops)
                          (eventFactsBdd `con` restrictSet (bddOf bls addlaw) [ (k, P k `elem` s) | P k <- vocabOf bls ])
                      of
                        []     -> error "no selected event"
                        [this] -> this
                        more   -> error $ "too many selected events: " ++ show more

-- TODO: test this!
instance Update MultipointedBelScene MultipointedEvent where
  checks = [haveSameAgents] -- no need to check precondition, we allow an empty set of actual states
  unsafeUpdate (bls@(BlS props _ _),statesBdd) (trfUnshifted, eventsBddUnshifted) =
    (newBls, newStatesBdd) where
      -- shiftPrepare first to ensure that eventsBdd is also shifted
      (trf@(Trf addprops _ changelaw _), shiftRel) = shiftPrepare bls trfUnshifted
      eventsBdd = relabelWith shiftRel eventsBddUnshifted
      (newBls, _) = unsafeUpdate (bls,undefined::State) (trf,undefined::State) -- using laziness!
      -- the actual event:
      changeprops = M.keys changelaw
      copyrel = zip changeprops [(freshp $ props ++ addprops)..]
      newStatesBdd = conSet [ relabelWith copyrel statesBdd, eventsBdd ]

-- ** Reduction Axioms

trfPost :: Event -> Prp -> Bdd
trfPost (Trf addprops _ changelaw _, x) p
  | p `elem` M.keys changelaw = restrictLaw (changelaw ! p) (booloutof x addprops)
  | otherwise                 = boolBddOf $ PrpF p

reduce :: Event -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = Just $ Neg $ preOf e
reduce e (PrpF p)     = Impl (preOf e) <$> Just (formOf $ trfPost e p)
reduce e (Neg f)      = Impl (preOf e) . Neg <$> reduce e f
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (preOf e) . Xor <$> mapM (reduce e) fs
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce e@(t@(Trf addprops _ _ eventObs), x) (K a f) =
  Impl (preOf e) . Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME is this a bit much?
                             , tagBddEval (mv x ++ cp y) (eventObs ! a)
    ]
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce e@(t@(Trf addprops _ _ eventObs), x) (Dk ags f) =
  Impl (preOf e) . Conj <$> sequence
    [Dk ags <$> reduce (t, y) f |
       let omegai = Tagged $ foldr (con . untag) top [eventObs ! i | i <- ags] :: RelBDD,
       y <- powerset addprops,
       tagBddEval (mv x ++ cp y) omegai]
reduce e (Dkw ags f)     = reduce e (Disj [Dk ags f, Dk ags (Neg f)])
reduce _ (G _)           = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ Dia          {} = Nothing

-- TODO: factor out shifting in 'transform' and 'bddReduce' to one separate function?

-- | Boolean translation for formulas prefixed with a dynamic operator containing a transformer.
--
-- \[ \| [\mathcal{X},x]\phi \|_\mathcal{F} :=
--     {\| [x \sqsubseteq V^+] \theta^+ \|}_\mathcal{F}
--       \to
--         [V_-^\circ \mapsto V_-]
--           [x \sqsubseteq V^+]
--             [V_- \mapsto \theta_-(V_-)]
--               {\| \phi \|}_{\mathcal{F} \times \mathcal{X}} \]
--
-- where \([\cdot \mapsto \cdot]\) denotes simultaneous substitution
-- and \([x \sqsubseteq V^+]\) substitutes elements of \(x\) by \(\top\) and other variables from \(V^+\) by \(\bot\).
-- See Definition 2.10.4 in [MG2018].
bddReduce :: BelScene -> Event -> Form -> Bdd
bddReduce scn@(oldBls,_) event@(Trf addprops _ changelaw _, eventFacts) f =
  let
    changeprops = M.keys changelaw
    -- same as in 'transform', to ensure props and addprops are disjoint
    shiftaddprops = [(freshp $ vocabOf scn)..]
    shiftrel      = sort $ zip addprops shiftaddprops
    -- apply the shifting to addlaw and changelaw:
    changelawShifted = M.map (relabelWith shiftrel) changelaw
    (newBlS,_) = update scn event
    -- the actual event, shifted
    actualAss  = [ (shifted, P orig `elem` eventFacts) | (P orig, P shifted) <- shiftrel ]
    postconrel = [ (n, changelawShifted ! P n) | (P n) <- changeprops ]
    -- reversing V^o to V
    copychangeprops = [(freshp $ vocabOf scn ++ map snd shiftrel)..]
    copyrelInverse  = zip copychangeprops changeprops
  in
    imp (bddOf oldBls (preOf event)) $ -- 0. check if precondition holds
      relabelWith copyrelInverse $     -- 4. changepropscopies -> original changeprops
        (`restrictSet` actualAss) $    -- 3. restrict to actual event x outof V+
          substitSimul postconrel $    -- 2. replace changeprops with postconditions
            bddOf newBlS f             -- 1. boolean equivalent wrt new structure

-- Note that in step 2 above we do a simultaneous substitution with `substitSimul` from HasCacBDD.

-- | Symbolically evaluate a formula starting with an event box using `evalViaBddReduce`.
evalViaBddReduce :: BelScene -> Event -> Form -> Bool
evalViaBddReduce (bls,s) event f = evaluateFun (bddReduce (bls,s) event f) (\n -> P n `elem` s)
