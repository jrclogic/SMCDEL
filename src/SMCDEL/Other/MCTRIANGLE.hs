{- |
This module implements an alternative representation of the Muddy Children, as proposed in:

- Nina Gierasimczuk, Jakub Szymanik (2011):
  /A note on a generalization of the Muddy Children puzzle/.
  <https://doi.org/10.1145/2000378.2000409>

The main idea is to not distinguish individual children who are in the same state which also means that their observations are the same.
Sections of Pascal's triangle can then be used to solve the Muddy Children puzzle in a Kripke model with less worlds than needed in the classical analysis, namely \(2n+1\) instead of \(2^n\) for \(n\) children.

-}
module SMCDEL.Other.MCTRIANGLE where

-- |A child can be muddy or clean.
data Kind = Muddy | Clean

-- | States are pairs of integers indicating how many children are (clean,muddy).
type State = (Int,Int)

-- | A muddy children model consists of three things: A list of observational states, a list of factual states and a current state.
data McModel = McM [State] [State] State deriving Show

-- | Create a muddy children model
mcModel :: State -> McModel
mcModel cur@(c,m) = McM ostates fstates cur where
  total   = c + m
  ostates = [ ((total-1)-m',m') | m'<-[0..(total-1)] ] -- observational states
  fstates = [ (total-m',    m') | m'<-[0..total    ] ] -- factual states

-- | Get the available successors of a state in a model
posFrom :: McModel -> State -> [State]
posFrom (McM _ fstates _) (oc,om) = filter (`elem` fstates) [ (oc+1,om), (oc,om+1) ]

-- | Get the observational state of an agent
obsFor :: McModel -> Kind -> State
obsFor (McM _ _ (curc,curm)) Clean = (curc-1,curm)
obsFor (McM _ _ (curc,curm)) Muddy = (curc,curm-1)

-- | Get all states deemed possible by an agent
posFor :: McModel -> Kind -> [State]
posFor m status = posFrom m $ obsFor m status

{- |
Note that instead of naming or enumerating agents we only distinguish two
Kind`s, the muddy and non-muddy ones, represented by Haskells constants
Muddy` and Clean` which allow pattern matching.
-}


-- | Quantifiers on the number triangle, e.g. `some`.
type Quantifier = State -> Bool

-- | The "some" quantifier.
some :: Quantifier
some (_,b) = b > 0

-- | The paper does not give a formal language definition, so here is our suggestion:
-- \[ \phi ::= \lnot \phi \mid  \bigwedge \Phi  \mid  Q  \mid  K_b \mid \overline{K}_b \]
-- where $\Phi$ ranges over finite sets of formulas, $b$ over $\{0,1\}$ and $Q$
-- over generalized quantifiers.
-- Note that when there are no agents of kind ``b`, the formulas
-- `KnowSelf b` and `NotKnowSelf b` are both true.
-- Hence `Neg (KnowSelf b)` and `NotKnowSelf b` are not the same!
data McFormula = Neg McFormula    -- negations
               | Conj [McFormula] -- conjunctions
               | Qf Quantifier    -- quantifiers
               | KnowSelf Kind    -- all b agents DO    know their status
               | NotKnowSelf Kind -- all b agents DON'T know their status

-- | Formula for ``Nobody knows their own state.''
nobodyknows :: McFormula
nobodyknows   = Conj [ NotKnowSelf Clean, NotKnowSelf Muddy ]

-- | Formula for ``Everybody knows their own state.''
everyoneKnows :: McFormula
everyoneKnows = Conj [    KnowSelf Clean,    KnowSelf Muddy ]

{- |
Note that in contrast to the standard DEL language the formulas are
independent of how many children there are. This is due to our identification
of agents with the same state and observations.
-}

-- | The semantics for the minimal language.
-- The four nullary knowledge operators can be thought of as
--   ``All agents who are (not) muddy do (not) know their own state.''
-- Hence they are vacuously true whenever there are no such agents.
-- If there are, the agents do know their state iff they consider only one
-- possibility (i.e. their observational state has only one successor).
eval :: McModel -> McFormula -> Bool
eval m (Neg f)          = not $ eval m f
eval m (Conj fs)        = all (eval m) fs
eval (McM _ _ s) (Qf q) = q s
eval m@(McM _ _ (_,curm)) (KnowSelf    Muddy) = curm==0 || length (posFor m Muddy) == 1
eval m@(McM _ _ (curc,_)) (KnowSelf    Clean) = curc==0 || length (posFor m Clean) == 1
eval m@(McM _ _ (_,curm)) (NotKnowSelf Muddy) = curm==0 || length (posFor m Muddy) == 2
eval m@(McM _ _ (curc,_)) (NotKnowSelf Clean) = curc==0 || length (posFor m Clean) == 2

-- | Update models with a formula:
mcUpdate :: McModel -> McFormula -> McModel
mcUpdate (McM ostates fstates cur) f =
  McM ostates' fstates' cur where
    fstates' = filter (\s -> eval (McM ostates fstates s) f) fstates
    ostates' = filter (not . null . posFrom (McM [] fstates' cur)) ostates

-- | Compute the n-th step of the puzzle, given an actual state.
step :: State -> Int -> McModel
step s 0 = mcUpdate (mcModel s) (Qf some)
step s n = mcUpdate (step s (n-1)) nobodyknows

-- | Show all steps of the puzzle, given an actual state.
showme :: State -> IO ()
showme s@(_,m) = mapM_ (\n -> putStrLn $ show n ++ ": " ++ show (step s n)) [0..(m-1)]

{- |
==== __Examples__

>>> showme (1,2)
m0: McM [(2,0),(1,1),(0,2)] [(2,1),(1,2),(0,3)] (1,2)
m1: McM [(1,1),(0,2)] [(1,2),(0,3)] (1,2)
-}
