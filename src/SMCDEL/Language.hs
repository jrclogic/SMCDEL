{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ExistentialQuantification, InstanceSigs #-}

{- |
This module defines the language of Dynamic Epistemic Logic (DEL).
Keeping the syntax definition separate from the semantics allows us to use
the same language throughout the whole report, for both the explicit and
the symbolic model checkers.
-}

module SMCDEL.Language where

import Data.List (nub,intercalate,(\\))
import Data.Maybe (fromMaybe)
import Data.Typeable (Typeable)

import Test.QuickCheck
import SMCDEL.Internal.Help (powerset,subseteq)
import SMCDEL.Internal.TexDisplay

-- * Propositions and Agents

{- $
Propositions are represented as integers in Haskell.
Agents are strings.
-}

newtype Prp = P Int deriving (Eq,Ord,Show)

instance Enum Prp where
  toEnum = P
  fromEnum (P n) = n

defaultVocabulary :: [Prp]
defaultVocabulary = map P [0..4]

instance Arbitrary Prp where
  arbitrary = elements defaultVocabulary

freshp :: [Prp] -> Prp
freshp []   = P 1
freshp prps = P (maximum (map fromEnum prps) + 1)

class HasVocab a where
  -- | What is the full vocabulary of this object?
  vocabOf :: a -> [Prp]

class UsesVocab a where
  -- | Which propositions occur in this object?
  -- Can be a part of the full vocabulary we work with.
  propsIn :: a -> [Prp]
  -- | Replace/substitute the propositions in the given object.
  replPsIn :: [(Prp,Prp)] -> a -> a

instance UsesVocab Prp where
  propsIn p = [p]
  replPsIn repl p = fromMaybe p (lookup p repl)

instance UsesVocab a => UsesVocab [a] where
  propsIn xs = nub $ concatMap propsIn xs
  replPsIn repl = map (replPsIn repl)

type Agent = String

alice,bob,carol :: Agent
alice = "Alice"
bob   = "Bob"
carol = "Carol"

-- | Five default agents given by `"1"` to `"5"`.
defaultAgents :: [Agent]
defaultAgents = map show [(1::Integer)..5]

newtype AgAgent = Ag Agent deriving (Eq,Ord,Show)

instance Arbitrary AgAgent where
  arbitrary = elements $ map Ag defaultAgents

-- | A group is a non-empty list of agents.
newtype Group = Group [Agent] deriving (Eq,Ord,Show)

instance Arbitrary Group where
  -- | Generate a random group, always including agent @"1"@.
  arbitrary = fmap (Group.("1":)) $ sublistOf $ defaultAgents \\ ["1"]

{- * Formulas
-}

{- $
The language \( \mathcal{L}(V) \) for a set of propositions \(V\) and a finite set of agents \(I\) is given by
  \[ \phi ::=
          \top   \mid  \bot  \mid  p
    \mid  \lnot \phi
    \mid  \bigwedge \Phi  \mid  \bigvee \Phi  \mid  \bigoplus \Phi
    \mid  \phi \rightarrow \phi  \mid  \phi \leftrightarrow \phi
    \mid  \forall P \phi  \mid  \exists P \phi
    \mid  K_i \phi  \mid  C_\Delta \phi \mid D_\Delta \phi
    \mid  [!\phi] \phi
    \mid  \langle \mathsf{DYN} \rangle \phi
where \(p \in V\), \(P \subseteq V\), \(|P|<\omega\), \(\Phi\subseteq\mathcal{L}(V)\), \(|\Phi|<\omega\), \(i \in I\), \(\Delta \subset I\) and \(\mathsf{DYN}\) is of an arbitrary type.
We also write \(\phi \land \psi\) for \(\bigwedge \{ \phi, \psi \}\) and \(\phi \lor \psi\) for \(\bigvee \{ \phi, \psi \}\).
The \emph{boolean} formulas are those without \(K_i\), \(C_\Delta\), \(D_\Delta\), \([!\phi]\) and \([\Delta!\phi]\).

Hence, a formula can be (in this order):
The constant top or bottom, an atomic proposition, a negation, a conjunction, a disjunction, an exclusive or, an implication, a bi-implication, a universal or existential quantification over a set of propositions, or a statement about knowledge, common-knowledge, distributed knowledge, a public announcement or a dynamic diamond.

Some of these connectives are inter-definable, for example \(\phi\leftrightarrow\psi\) and \(\bigwedge \{ \psi\rightarrow\phi,\phi\rightarrow\psi \}\) are equivalent according to all semantics which we will use here.
Hence we could shorten Definition~\ref{def-dellang} and treat some connectives as abbreviations.
This would lead to brevity and clarity in the formal definitions, but also to a decrease in performance of our model checking implementations.
To continue with the first example: If we have Binary Decision Diagrams (BDDs) for \(\phi\) and \(\psi\), computing the BDD for \(\phi\leftrightarrow\psi\) in one operation by calling the appropriate method of a BDD package will be faster than rewriting it to a conjunction of two implications and then making three calls to these corresponding functions of the BDD package.

We extend our language with abbreviations for "knowing whether", "commonly knowing whether" and "distributed knowing whether":

\[ K^?_i \phi := \bigvee \{ K_i \phi , K_i (\lnot \phi) \} \]

\[ C^?_\Delta \phi := \bigvee \{ C_\Delta \phi , C_\Delta (\lnot \phi) \} \]

\[ D^?_\Delta \phi := \bigvee \{ D_\Delta \phi , D_\Delta (\lnot \phi) \} \]

For performance reasons these "whether" operators are primitives and not abbreviations.
-}

-- | Formulas
data Form
  = Top                         -- ^ True Constant
  | Bot                         -- ^ False Constant
  | PrpF Prp                    -- ^ Atomic Proposition
  | Neg Form                    -- ^ Negation
  | Conj [Form]                 -- ^ n-ary Conjunction
  | Disj [Form]                 -- ^ n-ary Disjunction
  | Xor [Form]                  -- ^ n-ary X-OR
  | Impl Form Form              -- ^ Implication
  | Equi Form Form              -- ^ Bi-Implication
  | Forall [Prp] Form           -- ^ Boolean Universal Quantification
  | Exists [Prp] Form           -- ^ Boolean Existential Quantification
  | K Agent Form                -- ^ Knowing that
  | Ck [Agent] Form             -- ^ Common knowing that
  | Dk [Agent] Form             -- ^ Distributed knowing that
  | Kw Agent Form               -- ^ Knowing whether
  | Ckw [Agent] Form            -- ^ Common knowing whether
  | Dkw [Agent] Form            -- ^ Distributed knowing whether
  | G Form                      -- ^ Global modality
  | PubAnnounce Form Form       -- ^ Public announcement that
  | Dia DynamicOp Form          -- ^ Dynamic Diamond
  deriving (Eq,Ord,Show)

-- * Abbreviations

-- | Binary conjunction
conj :: Form -> Form -> Form
conj f g = Conj [f, g]

-- | Binary disjunction
disj :: Form -> Form -> Form
disj f g = Disj [f, g]

-- | If-Then-Else
ite :: Form -> Form -> Form -> Form
ite f g h = Conj [f `Impl` g, Neg f `Impl` h]

-- | The epistemic diamond operator "considers possible that".
kHat :: Agent -> Form -> Form
kHat i f = Neg (K i (Neg f))

-- | Sequence of public announcements.
pubAnnounceStack :: [Form] -> Form -> Form
pubAnnounceStack = flip $ foldr PubAnnounce

-- | Announcement-whether
-- \([?! \phi] \psi := \bigwedge \{ \phi \rightarrow [!\phi]\psi , \lnot \phi \rightarrow [!\lnot\phi]\psi \} \)
pubAnnounceW :: Form -> Form -> Form
pubAnnounceW af f = Conj [ af `Impl` PubAnnounce af f
                         , Neg af `Impl` PubAnnounce (Neg af) f ]

-- | Sequence of public announcement-whether.
pubAnnounceWhetherStack :: [Form] -> Form -> Form
pubAnnounceWhetherStack = flip $ foldr pubAnnounceW

-- | Abbreviation to say that exactly a given subset of a set of propositions is true.
booloutofForm :: [Prp] -> [Prp] -> Form
booloutofForm ps qs = Conj [ (if p `elem` ps then id else Neg) (PrpF p) | p <- qs ]

-- | Exactly one formula in the given list is true.
oneOf :: [Form] -> Form
oneOf fs = Conj [ Disj fs, Conj [ Neg $ Conj [f1, f2] | f1 <- fs, f2 <- fs \\ [f1] ] ]

-- * Dynamic Operators

-- | The values of a type can be used as a dynamic operator in formulas
-- whenever we know how to show them, what agents occur in them and we
-- what the precondition of this operator is.
-- This does /not/ yet guarantee we can actually evaluate those formulas, as
-- this will depend on the semantics used. See also @Update@.
class (Typeable b, Show b, UsesAgents b, UsesVocab b, HasPrecondition b) => DynOp b

-- | A dynamic operator comes with a @String@ label, used for showing and equality.
data DynamicOp = forall a . DynOp a => Dyn String a

instance Eq DynamicOp where
  Dyn a _ == Dyn b _ = a == b
instance Ord DynamicOp where
  compare (Dyn a _) (Dyn b _) = compare a b
instance Show DynamicOp where
  show (Dyn a _) = "Dyn " ++ show a ++ " _"

instance UsesVocab DynamicOp where
  propsIn (Dyn _ op) = propsIn op
  replPsIn repl (Dyn l op) = Dyn l (replPsIn repl op)

instance UsesAgents DynamicOp where
  agentsIn (Dyn _ op) = agentsIn op

-- | The dynamic box operator
box :: DynamicOp -> Form -> Form
box op f = Neg (Dia op (Neg f))

-- * Type classes

-- ** Type Classes for Semantics

class HasAgents a where
  agentsOf :: a -> [Agent]

class UsesAgents a where
  -- | Which agents occur in this object?
  agentsIn :: a -> [Agent]

class (HasVocab a, HasAgents a) => Semantics a where
  isTrue :: a -> Form -> Bool

-- | The \(\vDash\) symbol for semantics.
(|=) :: Semantics a => a -> Form -> Bool
(|=) = isTrue

-- ** Type Classes for Pointed Models and Structures

class Pointed a b

class DefaultPoint a b where
  pointDef :: a -> (a,b)

instance (HasVocab a, Pointed a b) => HasVocab (a,b) where vocabOf = vocabOf . fst
instance (UsesVocab a, Pointed a b) => UsesVocab (a,b) where
  propsIn = propsIn . fst
  -- | NOTE: We assume that no replacement in xb is needed.
  -- This holds for (multi)pointed action models and transformers.
  replPsIn repl (xa, xb) = (replPsIn repl xa, xb)

instance (HasAgents a, Pointed a b) => HasAgents (a,b) where agentsOf = agentsOf . fst
instance (UsesAgents a, Pointed a b) => UsesAgents (a,b) where agentsIn = agentsIn . fst

class ToMulti a b where
  toMulti :: a -> b

class Optimizable a where
  optimize :: [Prp] -> a -> a

-- ** Type Classes for Updates

class HasPrecondition a where
  preOf :: a -> Form

-- | Formulas used as public announcements are their own precondition.
instance HasPrecondition Form where
  preOf = id

instance DynOp Form

class (Show a, Semantics a, DynOp b) => Update a b where
  {-# MINIMAL unsafeUpdate #-}
  unsafeUpdate :: a -> b -> a
  checks :: [a -> b -> Bool]
  checks = [preCheck]
  preCheck :: a -> b -> Bool
  preCheck x y = isTrue x (preOf y)
  update :: a -> b -> a
  update x y = if and checkResults
                 then unsafeUpdate x y
                 else error . concat $
                   [ "Update failed."
                   , "\n  x = ", show x
                   , "\n  y = ", show y
                   , "\n  preOf y = ", show (preOf y)
                   , "\n  preCheck x y = ", show (preCheck x y)
                   , "\n  checkResults: ", show checkResults ]
               where checkResults = [ c x y | c <- checks ]

-- | Execute a list of updates, return the final resulting state.
updates :: Update a b => a -> [b] -> a
updates = foldl update

-- | Execute a list of updates, return the list of starting, intermediate and final result states.
updateSequence :: Update a b => a -> [b] -> [a]
updateSequence x []    = [x]
updateSequence x (y:ys) = let next = x `update` y in x : updateSequence next ys

-- | All agents used in the second argument exist in the first. -- TODO rename this!
haveSameAgents :: (HasAgents a, UsesAgents b) => a -> b -> Bool
haveSameAgents x y = agentsIn y `subseteq` agentsOf x

-- * Pretty-printing

showSet :: Show a => [a] -> String
showSet xs = intercalate "," (map show xs)

-- | Pretty-print a formula.
ppForm :: Form -> String
ppForm = ppFormWith (\(P n) -> show n)

-- | Pretty-print a formula with a translation for atomic propositions.
ppFormWith :: (Prp -> String)-> Form -> String
ppFormWith _     Top           = "T"
ppFormWith _     Bot           = "F"
ppFormWith trans (PrpF p)      = trans p
ppFormWith trans (Neg f)       = "~" ++ ppFormWith trans f
ppFormWith trans (Conj fs)     = "(" ++ intercalate " & " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Disj fs)     = "(" ++ intercalate " | " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Xor fs)      = "XOR{" ++ showSet (map (ppFormWith trans) fs) ++ "}"
ppFormWith trans (Impl f g)    = "(" ++ ppFormWith trans f ++ "->" ++ ppFormWith trans g ++ ")"
ppFormWith trans (Equi f g)    = ppFormWith trans f ++ "=" ++ ppFormWith trans g
ppFormWith trans (Forall ps f) = "Forall {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (Exists ps f) = "Exists {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (K i f)       = "K " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ck is f)     = "Ck " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (Dk is f)     = "Dk " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (Kw i f)      = "Kw " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ckw is f)    = "Ckw " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (Dkw is f)    = "Dkw " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (G      f)    = "G " ++ ppFormWith trans f
ppFormWith trans (PubAnnounce f g)  = "[! " ++ ppFormWith trans f ++ "] " ++ ppFormWith trans g
ppFormWith trans (Dia (Dyn s _) f)  = "<" ++ s ++ ">" ++ ppFormWith trans f

-- | Generates LaTeX code for a formula.
texForm :: Form -> String
texForm Top           = "\\top "
texForm Bot           = "\\bot "
texForm (PrpF p)      = tex p
texForm (Neg (PubAnnounce f (Neg g))) = "\\langle !" ++ texForm f ++ " \\rangle " ++ texForm g
texForm (Neg f)       = "\\lnot " ++ texForm f
texForm (Conj [])     = "\\top "
texForm (Conj [f])    = texForm f
texForm (Conj [f,g])  = " ( " ++ texForm f ++ " \\land " ++ texForm g ++" ) "
texForm (Conj fs)     = "\\bigwedge \\{\n" ++ intercalate "," (map texForm fs) ++" \\} "
texForm (Disj [])     = "\\bot "
texForm (Disj [f])    = texForm f
texForm (Disj [f,g])  = " ( " ++ texForm f ++ " \\lor "++ texForm g ++ " ) "
texForm (Disj fs)     = "\\bigvee \\{\n " ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Xor [])      = "\\bot "
texForm (Xor [f])     = texForm f
texForm (Xor [f,g])   = " ( " ++ texForm f  ++ " \\oplus " ++ texForm g ++ " ) "
texForm (Xor fs)      = "\\bigoplus \\{\n" ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Equi f g)    = " ( "++ texForm f ++" \\leftrightarrow "++ texForm g ++" ) "
texForm (Impl f g)    = " ( "++ texForm f ++" \\rightarrow "++ texForm g ++" ) "
texForm (Forall ps f) = " \\forall " ++ tex ps ++ " " ++ texForm f
texForm (Exists ps f) = " \\exists " ++ tex ps ++ " " ++ texForm f
texForm (K i f)       = "K_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Kw i f)      = "K^?_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Ck ags f)    = "Ck_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (Dk ags f)    = "Dk_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (Ckw ags f)   = "Ck^?_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (Dkw ags f)   = "Dk^?_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (G f)         = "G " ++ texForm f
texForm (PubAnnounce f g)   = "[!" ++ texForm f ++ "] " ++ texForm g
texForm (Dia (Dyn s _) f)   = " \\langle \\text{" ++ s ++ "} \\rangle " ++ texForm f

instance TexAble Prp where
  tex (P 0) = " p "
  tex (P n) = " p_{" ++ show n ++ "} "

instance TexAble [Prp] where
  tex [] = " \\varnothing "
  tex ps = "\\{" ++ intercalate "," (map tex ps) ++ "\\}"

instance TexAble Form where
  tex f = " \\ensuremath{ " ++ removeDoubleSpaces (texForm f) ++ " } "

-- * Subformulas and Shrinking

-- | List of subformulas, including the given formula itself.
-- In particular this is used in the `shrink` function for QuickCheck.
subformulas :: Form -> [Form]
subformulas Top           = [Top]
subformulas Bot           = [Bot]
subformulas (PrpF p)      = [PrpF p]
subformulas (Neg f)       = Neg f : subformulas f
subformulas (Conj fs)     = Conj fs : nub (concatMap subformulas fs)
subformulas (Disj fs)     = Disj fs : nub (concatMap subformulas fs)
subformulas (Xor fs)      = Xor  fs : nub (concatMap subformulas fs)
subformulas (Impl f g)    = Impl f g : nub (concatMap subformulas [f,g])
subformulas (Equi f g)    = Equi f g : nub (concatMap subformulas [f,g])
subformulas (Forall ps f) = Forall ps f : subformulas f
subformulas (Exists ps f) = Exists ps f : subformulas f
subformulas (K i f)       = K i f : subformulas f
subformulas (Ck is f)     = Ck is f : subformulas f
subformulas (Dk is f)     = Dk is f : subformulas f
subformulas (Kw i f)      = Kw i f : subformulas f
subformulas (Ckw is f)    = Ckw is f : subformulas f
subformulas (Dkw is f)    = Dkw is f : subformulas f
subformulas (G f)         = G f : subformulas f
subformulas (PubAnnounce  f g) = PubAnnounce  f g : nub (subformulas f ++ subformulas g)
subformulas (Dia dynop f)      = Dia dynop f : subformulas f

shrinkform :: Form -> [Form]
shrinkform f = [ simplify f | f /= simplify f ] ++ (subformulas f \\ [f]) ++ otherShrinks f
  where
    otherShrinks (Conj     fs) = [Conj     gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Disj     fs) = [Disj     gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Xor      fs) = [Xor      gs | gs <- powerset fs \\ [fs]]
    otherShrinks (Ck     is g) = [Ck     js g | js <- powerset is \\ [is], not (null js)]
    otherShrinks (Ckw    is g) = [Ckw    js g | js <- powerset is \\ [is], not (null js)]
    otherShrinks (Dk     is g) = [Dk     js g | js <- powerset is \\ [is], not (null js)]
    otherShrinks (Dkw    is g) = [Dkw    js g | js <- powerset is \\ [is], not (null js)]
    otherShrinks (Forall ps g) = [Forall qs g | qs <- powerset ps \\ [ps]]
    otherShrinks (Exists ps g) = [Exists qs g | qs <- powerset ps \\ [ps]]
    otherShrinks _ = []

-- | Does the formula contain a global modality?
containsGlobal :: Form -> Bool
containsGlobal f = or [ True | (G _) <- subformulas f ]

-- * Substitution

-- | Substitute a formula for a proposition in a formula.
-- As a safety measure this method will fail whenever the proposition to be replaced occurs in a quantifier.
-- All other cases are done by recursion.
substit :: Prp -> Form -> Form -> Form
substit _ _   Top           = Top
substit _ _   Bot           = Bot
substit q psi (PrpF p)      = if p==q then psi else PrpF p
substit q psi (Neg form)    = Neg (substit q psi form)
substit q psi (Conj forms)  = Conj (map (substit q psi) forms)
substit q psi (Disj forms)  = Disj (map (substit q psi) forms)
substit q psi (Xor  forms)  = Xor  (map (substit q psi) forms)
substit q psi (Impl f g)    = Impl (substit q psi f) (substit q psi g)
substit q psi (Equi f g)    = Equi (substit q psi f) (substit q psi g)
substit q psi (Forall ps f) = if q `elem` ps
  then error ("substit failed: Substituens "++ show q ++ " in 'Forall " ++ show ps ++ " " ++ show f)
  else Forall ps (substit q psi f)
substit q psi (Exists ps f) = if q `elem` ps
  then error ("substit failed: Substituens " ++ show q ++ " in 'Exists " ++ show ps ++ " " ++ show f)
  else Exists ps (substit q psi f)
substit q psi (K  i f)     = K  i (substit q psi f)
substit q psi (Kw i f)     = Kw i (substit q psi f)
substit q psi (Ck ags f)   = Ck ags (substit q psi f)
substit q psi (Ckw ags f)  = Ckw ags (substit q psi f)
substit q psi (Dk ags f)   = Dk ags (substit q psi f)
substit q psi (Dkw ags f)  = Dkw ags (substit q psi f)
substit q psi (G f)        = G (substit q psi f)
substit q psi (PubAnnounce f g)   = PubAnnounce (substit q psi f) (substit q psi g)
substit _ _   (Dia _ _)           = error "Cannot substitute in dynamic diamonds."

-- | Apply multiple substitutions after each other.
-- Note: in general this is *not* the same as simultaneous substitution.
-- It is equivalent to simultaneous substitution if none of the
-- replaced propositions occurs in the replacement formulas.
substitSet :: [(Prp,Form)] -> Form -> Form
substitSet []             f = f
substitSet ((q,psi):rest) f = substitSet rest (substit q psi f)

-- | The "out of" substitution \([A \sqsubseteq B]\phi\).
substitOutOf :: [Prp] -> [Prp] -> Form -> Form
substitOutOf truths allps = substitSet [(p, if p `elem` truths then Top else Bot) | p <- allps]

-- * Vocabulary of a formula

instance UsesVocab Form where
  -- | List of all propositions occurring in a formula.
  propsIn :: Form -> [Prp]
  propsIn Top                = []
  propsIn Bot                = []
  propsIn (PrpF p)           = [p]
  propsIn (Neg f)            = propsIn f
  propsIn (Conj fs)          = nub $ concatMap propsIn fs
  propsIn (Disj fs)          = nub $ concatMap propsIn fs
  propsIn (Xor  fs)          = nub $ concatMap propsIn fs
  propsIn (Impl f g)         = nub $ concatMap propsIn [f,g]
  propsIn (Equi f g)         = nub $ concatMap propsIn [f,g]
  propsIn (Forall ps f)      = nub $ ps ++ propsIn f
  propsIn (Exists ps f)      = nub $ ps ++ propsIn f
  propsIn (K _ f)            = propsIn f
  propsIn (Kw _ f)           = propsIn f
  propsIn (Ck _ f)           = propsIn f
  propsIn (Ckw _ f)          = propsIn f
  propsIn (Dk _ f)           = propsIn f
  propsIn (Dkw _ f)          = propsIn f
  propsIn (G f)              = propsIn f
  propsIn (PubAnnounce f g)  = nub $ propsIn f ++ propsIn g
  propsIn (Dia op f)         = nub $ propsIn op ++ propsIn f -- uses HasVocab DynamicOp
  -- | Replace propositions in a formula.
  -- In contrast to the previous substitution function this *is* simultaneous.
  replPsIn :: [(Prp,Prp)] -> Form -> Form
  replPsIn _       Top      = Top
  replPsIn _       Bot      = Bot
  replPsIn repl (PrpF p)    = PrpF $ replPsIn repl p
  replPsIn repl (Neg f)     = Neg $ replPsIn repl f
  replPsIn repl (Conj fs)   = Conj $ map (replPsIn repl) fs
  replPsIn repl (Disj fs)   = Disj $ map (replPsIn repl) fs
  replPsIn repl (Xor  fs)   = Xor  $ map (replPsIn repl) fs
  replPsIn repl (Impl f g)  = Impl (replPsIn repl f) (replPsIn repl g)
  replPsIn repl (Equi f g)  = Equi (replPsIn repl f) (replPsIn repl g)
  replPsIn repl (Forall ps f) = Forall (map (replPsIn repl) ps) (replPsIn repl f)
  replPsIn repl (Exists ps f) = Exists (map (replPsIn repl) ps) (replPsIn repl f)
  replPsIn repl (K i f)     = K i (replPsIn repl f)
  replPsIn repl (Kw i f)    = Kw i (replPsIn repl f)
  replPsIn repl (Ck ags f)  = Ck ags (replPsIn repl f)
  replPsIn repl (Ckw ags f) = Ckw ags (replPsIn repl f)
  replPsIn repl (Dk ags f)  = Dk ags (replPsIn repl f)
  replPsIn repl (Dkw ags f) = Dkw ags (replPsIn repl f)
  replPsIn repl (G f)       = G (replPsIn repl f)
  replPsIn repl (PubAnnounce f g)   = PubAnnounce   (replPsIn repl f) (replPsIn repl g)
  replPsIn repl (Dia op f)  = Dia (replPsIn repl op) (replPsIn repl f)

instance UsesAgents Form where
  -- | List of all agents occurring in a formula.
  agentsIn :: Form -> [Agent]
  agentsIn Top                = []
  agentsIn Bot                = []
  agentsIn (PrpF _)           = []
  agentsIn (Neg f)            = agentsIn f
  agentsIn (Conj fs)          = nub $ concatMap agentsIn fs
  agentsIn (Disj fs)          = nub $ concatMap agentsIn fs
  agentsIn (Xor  fs)          = nub $ concatMap agentsIn fs
  agentsIn (Impl f g)         = nub $ concatMap agentsIn [f,g]
  agentsIn (Equi f g)         = nub $ concatMap agentsIn [f,g]
  agentsIn (Forall _ f)       = agentsIn f
  agentsIn (Exists _ f)       = agentsIn f
  agentsIn (K i f)            = nub $ i : agentsIn f
  agentsIn (Kw i f)           = nub $ i : agentsIn f
  agentsIn (Ck is f)          = nub $ is ++ agentsIn f
  agentsIn (Ckw is f)         = nub $ is ++ agentsIn f
  agentsIn (Dk is f)          = nub $ is ++ agentsIn f
  agentsIn (Dkw is f)         = nub $ is ++ agentsIn f
  agentsIn (G f)              = agentsIn f
  agentsIn (PubAnnounce f g)  = nub $ agentsIn f ++ agentsIn g
  agentsIn (Dia op f)         = nub $ agentsIn op ++ agentsIn f -- this uses HasVocab DynamicOp

-- * Simplification

-- | Simplify a formula using boolean equivalences.
-- For example, remove double negations and ``bubble up'' \(\bot\)
-- and \(\top\) in conjunctions and disjunctions, respectively.
simplify :: Form -> Form
simplify f = if simStep f == f then f else simplify (simStep f)

simStep :: Form -> Form
simStep Top           = Top
simStep Bot           = Bot
simStep (PrpF p)      = PrpF p
simStep (Neg Top)     = Bot
simStep (Neg Bot)     = Top
simStep (Neg (Neg f)) = simStep f
simStep (Neg f)       = Neg $ simStep f
simStep (Conj [])     = Top
simStep (Conj [f])    = simStep f
simStep (Conj fs)     | Bot `elem` fs = Bot
                      | or [ Neg f `elem` fs | f <- fs ] = Bot
                      | otherwise     = Conj (nub $ concatMap unpack fs) where
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
simStep (Disj [])     = Bot
simStep (Disj [f])    = simStep f
simStep (Disj fs)     | Top `elem` fs = Top
                      | or [ Neg f `elem` fs | f <- fs ] = Top
                      | otherwise     = Disj (nub $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Xor  [])     = Bot
simStep (Xor  [Bot])  = Bot
simStep (Xor  [f])    = simStep f
simStep (Xor  fs)     = Xor (map simStep $ filter (Bot /=) fs)
simStep (Impl Bot _)  = Top
simStep (Impl _ Top)  = Top
simStep (Impl Top f)  = simStep f
simStep (Impl f Bot)  = Neg (simStep f)
simStep (Impl f g)    | f==g      = Top
                      | otherwise = Impl (simStep f) (simStep g)
simStep (Equi Top f)  = simStep f
simStep (Equi Bot f)  = Neg (simStep f)
simStep (Equi f Top)  = simStep f
simStep (Equi f Bot)  = Neg (simStep f)
simStep (Equi f g)    | f==g      = Top
                      | otherwise = Equi (simStep f) (simStep g)
simStep (Forall [] f) = simStep f
simStep (Forall ps f) = Forall ps (simStep f)
simStep (Exists [] f) = simStep f
simStep (Exists ps f) = Exists ps (simStep f)
simStep (K a f)       = K a (simStep f)
simStep (Kw a f)      = Kw a (simStep f)
simStep (Ck _   Top)  = Top
simStep (Ck ags Bot)  = Ck ags Bot -- Not equivalent to Bot in K.
simStep (Ck ags f)    = Ck ags (simStep f)
simStep (Ckw _   Top) = Top
simStep (Ckw _   Bot) = Top
simStep (Ckw ags f)   = Ckw ags (simStep f)
simStep (Dk _   Top)  = Top
simStep (Dk ags Bot)  = Dk ags Bot -- Not equivalent to Bot in K.
simStep (Dk ags f)    = Dk ags (simStep f)
simStep (Dkw _   Top) = Top
simStep (Dkw _   Bot) = Top
simStep (Dkw ags f)   = Dkw ags (simStep f)
simStep (G Top)       = Top
simStep (G f)         = G (simStep f)
simStep (PubAnnounce Top f) = simStep f
simStep (PubAnnounce Bot _) = Top
simStep (PubAnnounce  f g)  = PubAnnounce  (simStep f) (simStep g)
simStep (Dia dynop f)       = Dia dynop (simStep f)

{- $

==== __Example for simplify__

Consider this rather unnatural formula:

>>> let testForm = Forall [P 3] $ Equi (Disj [ Bot, PrpF $ P 3, Bot ]) (Conj [ Top , Xor [Top,Kw alice (PrpF (P 4))] , PubAnnounce (PrpF (P 5)) (Kw bob $ PrpF (P 5)) ])
>>> testForm
Forall [P 3] (Equi (Disj [Bot,PrpF (P 3),Bot]) (Conj [Top,Xor [Top,Kw "Alice" (PrpF (P 4))],PubAnnounce (PrpF (P 5)) (Kw "Bob" (PrpF (P 5)))]))
>>> simplify testForm
Forall [P 3] (Equi (PrpF (P 3)) (Conj [Xor [Top,Kw "Alice" (PrpF (P 4))],PubAnnounce (PrpF (P 5)) (Kw "Bob" (PrpF (P 5)))]))
-}

-- TODO: how to show TeX output in Haddock?

-- * Generating random formulas

-- | Boolean Formulas
newtype BF = BF Form deriving (Eq,Ord,Show)

instance Arbitrary BF where
  arbitrary = sized $ randomboolformWith defaultVocabulary
  shrink (BF f) = map BF $ shrinkform f

randomboolformWith :: [Prp] -> Int -> Gen BF
randomboolformWith allprops sz = BF <$> bf' sz where
  bf' 0 = PrpF <$> elements allprops
  bf' n = oneof [ pure SMCDEL.Language.Top
                , pure SMCDEL.Language.Bot
                , PrpF <$> elements allprops
                , Neg <$> st
                , (\x y -> Conj [x,y]) <$> st <*> st
                , (\x y z -> Conj [x,y,z]) <$> st <*> st <*> st
                , (\x y -> Disj [x,y]) <$> st <*> st
                , (\x y z -> Disj [x,y,z]) <$> st <*> st <*> st
                , Impl <$> st <*> st
                , Equi <$> st <*> st
                , (\x -> Xor [x]) <$> st
                , (\x y -> Xor [x,y]) <$> st <*> st
                , (\x y z -> Xor [x,y,z]) <$> st <*> st <*> st
                -- , (\p f -> Exists [p] f) <$> elements allprops <*> st
                -- , (\p f -> Forall [p] f) <$> elements allprops <*> st
                ]
    where
      st = bf' (n `div` 3)

-- | A general Arbitrary instance for formulas.
-- It is used heavily in the automated tests.
instance Arbitrary Form where
  arbitrary = sized form where
    form 0 = oneof [ pure Top
                   , pure Bot
                   , PrpF <$> arbitrary ]
    form n = oneof [ pure Top
                   , pure Bot
                   , PrpF <$> arbitrary
                   , Neg <$> form n'
                   , Conj <$> listOf (form n')
                   , Disj <$> listOf (form n')
                   , Xor  <$> listOf (form n')
                   , Impl <$> form n' <*> form n'
                   , Equi <$> form n' <*> form n'
                   , K   <$> arbitraryAg <*> form n'
                   , Ck  <$> arbitraryAgs <*> form n'
                   , Dk  <$> arbitraryAgs <*> form n'
                   , Kw  <$> arbitraryAg <*> form n'
                   , Ckw <$> arbitraryAgs <*> form n'
                   , Dkw <$> arbitraryAgs <*> form n'
                   , G <$> form n'
                   , PubAnnounce <$> form n' <*> form n'
                   ]
      where
        n' = n `div` 5
        arbitraryAg = (\(Ag i) -> i) <$> arbitrary
        arbitraryAgs = sublistOf (map show [1..(5::Integer)]) `suchThat` (not . null)
  shrink = shrinkform

newtype SimplifiedForm = SF Form deriving (Eq,Ord,Show)

-- | Simplified Formulas
instance Arbitrary SimplifiedForm where
  arbitrary = SF . simplify <$> arbitrary
  shrink (SF f) = nub $ map (SF . simplify) (shrinkform f)
