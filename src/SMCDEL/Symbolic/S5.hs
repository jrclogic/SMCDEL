{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

module SMCDEL.Symbolic.S5 where

import Control.Arrow (first,second,(***))
import Data.Char (isSpace)
import Data.Dynamic
import Data.HasCacBDD hiding (Top,Bot)
import Data.HasCacBDD.Visuals
import Data.List ((\\),delete,dropWhileEnd,intercalate,intersect,nub,sort)
import Data.Tagged
import System.Directory (findExecutable)
import System.IO (hPutStr, hGetContents, hClose)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (runInteractiveCommand)
import Test.QuickCheck

import SMCDEL.Internal.Help ((!),alleqWith,apply,applyPartial,lfp,powerset,rtc,seteq)
import SMCDEL.Internal.TaggedBDD
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.BDD2Form

boolBddOf :: Form -> Bdd
boolBddOf Top           = top
boolBddOf Bot           = bot
boolBddOf (PrpF (P n))  = var n
boolBddOf (Neg form)    = neg$ boolBddOf form
boolBddOf (Conj forms)  = conSet $ map boolBddOf forms
boolBddOf (Disj forms)  = disSet $ map boolBddOf forms
boolBddOf (Xor forms)   = xorSet $ map boolBddOf forms
boolBddOf (Impl f g)    = imp (boolBddOf f) (boolBddOf g)
boolBddOf (Equi f g)    = equ (boolBddOf f) (boolBddOf g)
boolBddOf (Forall ps f) = forallSet (map fromEnum ps) (boolBddOf f)
boolBddOf (Exists ps f) = existsSet (map fromEnum ps) (boolBddOf f)
boolBddOf _             = error "boolBddOf failed: Not a boolean formula."

boolEvalViaBdd :: [Prp] -> Form -> Bool
boolEvalViaBdd truths = bddEval truths . boolBddOf

bddEval :: [Prp] -> Bdd -> Bool
bddEval truths querybdd = evaluateFun querybdd (\n -> P n `elem` truths)

relabelWith :: [(Prp,Prp)] -> Bdd -> Bdd
relabelWith r = relabel (sort $ map (fromEnum *** fromEnum) r)

data KnowStruct = KnS [Prp]            -- vocabulary
                      Bdd              -- state law
                      [(Agent,[Prp])]  -- observational variables
                    deriving (Eq,Show)

type State = [Prp]

instance Pointed KnowStruct State
type KnowScene = (KnowStruct,State)

instance Pointed KnowStruct Bdd
type MultipointedKnowScene = (KnowStruct,Bdd)

statesOf :: KnowStruct -> [State]
statesOf (KnS props lawbdd _) = map (sort.translate) resultlists where
  resultlists :: [[(Prp, Bool)]]
  resultlists = map (map (first toEnum)) $ allSatsWith (map fromEnum props) lawbdd
  translate l = map fst (filter snd l)

instance HasAgents KnowStruct where
  agentsOf (KnS _ _ obs)= map fst obs

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

numberOfStates :: KnowStruct -> Int
numberOfStates (KnS props lawbdd _) = satCountWith (map fromEnum props) lawbdd

shareknow :: KnowStruct -> [[Prp]] -> [(State,State)]
shareknow kns sets = filter rel [ (s,t) | s <- statesOf kns, t <- statesOf kns ] where
  rel (x,y) = or [ seteq (x `intersect` set) (y `intersect` set) | set <- sets ]

comknow :: KnowStruct -> [Agent] -> [(State,State)]
comknow kns@(KnS _ _ obs) ags = rtc $ shareknow kns (map (apply obs) ags)

eval :: KnowScene -> Form -> Bool
eval _       Top           = True
eval _       Bot           = False
eval (_,s)   (PrpF p)      = p `elem` s
eval (kns,s) (Neg form)    = not $ eval (kns,s) form
eval (kns,s) (Conj forms)  = all (eval (kns,s)) forms
eval (kns,s) (Disj forms)  = any (eval (kns,s)) forms
eval (kns,s) (Xor  forms)  = odd $ length (filter id $ map (eval (kns,s)) forms)
eval scn     (Impl f g)    = not (eval scn f) || eval scn g
eval scn     (Equi f g)    = eval scn f == eval scn g
eval scn     (Forall ps f) = eval scn (foldl singleForall f ps) where
  singleForall g p = Conj [ SMCDEL.Language.substit p Top g, SMCDEL.Language.substit p Bot g ]
eval scn     (Exists ps f) = eval scn (foldl singleExists f ps) where
  singleExists g p = Disj [ SMCDEL.Language.substit p Top g, SMCDEL.Language.substit p Bot g ]
eval (kns@(KnS _ _ obs),s) (K i form) = all (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (s' `intersect` oi) (s `intersect` oi)) (statesOf kns)
  oi = obs ! i
eval (kns@(KnS _ _ obs),s) (Kw i form) = alleqWith (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (s' `intersect` oi) (s `intersect` oi)) (statesOf kns)
  oi = obs ! i
eval (kns,s) (Ck ags form)  = all (\s' -> eval (kns,s') form) theres where
  theres = [ s' | (s0,s') <- comknow kns ags, s0 == s ]
eval (kns,s) (Ckw ags form)  = alleqWith (\s' -> eval (kns,s') form) theres where
  theres = [ s' | (s0,s') <- comknow kns ags, s0 == s ]
eval scn (PubAnnounce form1 form2) =
  not (eval scn form1) || eval (update scn form1) form2
eval (kns,s) (PubAnnounceW form1 form2) =
  if eval (kns, s) form1
    then eval (update kns form1, s) form2
    else eval (update kns (Neg form1), s) form2
eval scn (Announce ags form1 form2) =
  not (eval scn form1) || eval (announceOnScn scn ags form1) form2
eval scn (AnnounceW ags form1 form2) =
  if eval scn form1
    then eval (announceOnScn scn ags form1      ) form2
    else eval (announceOnScn scn ags (Neg form1)) form2
eval scn (Dia (Dyn dynLabel d) f) = case fromDynamic d of
  Just event -> eval scn (preOf (event :: Event))
                && eval (scn `update` event) f
  Nothing    -> error $ "cannot update knowledge structure with '" ++ dynLabel ++ "':\n  " ++ show d


announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = sort $ proppsi : props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, obs ! i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

announceOnScn :: KnowScene -> [Agent] -> Form -> KnowScene
announceOnScn (kns@(KnS props _ _),s) ags psi
  | eval (kns,s) psi = (announce kns ags psi, sort $ freshp props : s)
  | otherwise        = error "Liar!"

bddOf :: KnowStruct -> Form -> Bdd
bddOf _   Top           = top
bddOf _   Bot           = bot
bddOf _   (PrpF (P n))  = var n
bddOf kns (Neg form)    = neg $ bddOf kns form
bddOf kns (Conj forms)  = conSet $ map (bddOf kns) forms
bddOf kns (Disj forms)  = disSet $ map (bddOf kns) forms
bddOf kns (Xor  forms)  = xorSet $ map (bddOf kns) forms
bddOf kns (Impl f g)    = imp (bddOf kns f) (bddOf kns g)
bddOf kns (Equi f g)    = equ (bddOf kns f) (bddOf kns g)
bddOf kns (Forall ps f) = forallSet (map fromEnum ps) (bddOf kns f)
bddOf kns (Exists ps f) = existsSet (map fromEnum ps) (bddOf kns f)
bddOf kns@(KnS allprops lawbdd obs) (K i form) =
  forallSet otherps (imp lawbdd (bddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ obs ! i
bddOf kns@(KnS allprops lawbdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawbdd (bddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ obs ! i
bddOf kns@(KnS allprops lawbdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ bddOf kns form : [ forallSet (otherps i) (imp lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ obs ! i
bddOf kns (Ckw ags form) = dis (bddOf kns (Ck ags form)) (bddOf kns (Ck ags (Neg form)))
bddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  imp (bddOf kns form1) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce kns ags form1) form2
    (P k) = freshp props
bddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  ifthenelse (bddOf kns form1) bdd2a bdd2b where
    bdd2a = restrict (bddOf (announce kns ags form1) form2) (k,True)
    bdd2b = restrict (bddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
bddOf kns (PubAnnounce form1 form2) =
  imp (bddOf kns form1) (bddOf (update kns form1) form2)
bddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (bddOf kns form1) newform2a newform2b where
    newform2a = bddOf (update kns form1) form2
    newform2b = bddOf (update kns (Neg form1)) form2

bddOf kns (Dia (Dyn dynLabel d) f) =
    con (bddOf kns preCon)                    -- 5. Prefix with "precon AND ..." (diamond!)
    . relabelWith copyrelInverse              -- 4. Copy back changeProps V_-^o to V_-
    . simulateActualEvents                    -- 3. Simulate actual event(s) [see below]
    . substitSimul [ (k, changeLaw ! p)       -- 2. Replace changeProps V_ with postcons
                   | p@(P k) <- changeProps]  --    (no "relabelWith copyrel", undone in 4)
    . bddOf (kns `update` trf)                -- 1. boolean equivalent wrt new struct
    $ f
  where
    changeProps = map fst changeLaw
    copychangeProps = [(freshp $ vocabOf kns ++ addProps)..]
    copyrelInverse  = zip copychangeProps changeProps
    (trf@(KnTrf addProps addLaw changeLaw _), shiftrel) = shiftPrepare kns trfUnshifted
    (preCon,trfUnshifted,simulateActualEvents) =
      case fromDynamic d of
        -- 3. For a single event, simulate actual event x outof V+
        Just ((t,x) :: Event) -> ( preOf (t,x), t, (`restrictSet` actualAss) )
          where actualAss = [(newK, P k `elem` x) | (P k, P newK) <- shiftrel]
        Nothing -> case fromDynamic d of
          -- 3. For a multipointed event, simulate a set of actual events by ...
          Just ((t,xsBdd) :: MultipointedEvent) ->
              ( preOf (t,xsBdd), t
              , existsSet (map fromEnum addProps)  -- ... replacing addProps with assigments
                . con actualsBdd                   -- ... that satisfy actualsBdd
                . con (bddOf kns addLaw)           -- ... and a precondition.
              ) where actualsBdd = relabelWith shiftrel xsBdd
          Nothing -> error $ "cannot update knowledge structure with '" ++ dynLabel ++ "':\n " ++ show d

evalViaBdd :: KnowScene -> Form -> Bool
evalViaBdd (kns,s) f = evaluateFun (bddOf kns f) (\n -> P n `elem` s)

instance Semantics KnowStruct where
  isTrue = validViaBdd

instance Semantics KnowScene where
  isTrue = evalViaBdd

instance Semantics MultipointedKnowScene where
  isTrue (kns@(KnS _ lawBdd _),statesBdd) f =
    let a = lawBdd `imp` (statesBdd `imp` bddOf kns f)
     in a == top

instance Update KnowStruct Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate kns@(KnS props lawbdd obs) psi =
    KnS props (lawbdd `con` bddOf kns psi) obs

instance Update KnowScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi,s)

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f

whereViaBdd :: KnowStruct -> Form -> [State]
whereViaBdd kns@(KnS props lawbdd _) f =
 map (sort . map (toEnum . fst) . filter snd) $
   allSatsWith (map fromEnum props) $ con lawbdd (bddOf kns f)

determinedVocabOf :: KnowStruct -> [Prp]
determinedVocabOf strct =
  filter (\p -> validViaBdd strct (PrpF p) || validViaBdd strct (Neg $ PrpF p)) (vocabOf strct)

nonobsVocabOf  :: KnowStruct -> [Prp]
nonobsVocabOf (KnS vocab _ obs) = filter (`notElem` concatMap snd obs) vocab

equivExtraVocabOf :: [Prp] -> KnowStruct -> [(Prp,Prp)]
equivExtraVocabOf mainVocab kns =
  [ (p,q) | p <- vocabOf kns \\ mainVocab, q <- vocabOf kns, p > q, validViaBdd kns (PrpF p `Equi` PrpF q) ]

replaceWithIn :: (Prp,Prp) -> KnowStruct -> KnowStruct
replaceWithIn (p,q) (KnS oldProps oldLaw oldObs) =
  KnS
    (delete p oldProps)
    (Data.HasCacBDD.substit (fromEnum p) (var (fromEnum q)) oldLaw)
    [(i, if p `elem` os then sort $ nub (q : delete p os) else os) | (i,os) <- oldObs]

replaceEquivExtra :: [Prp] -> KnowStruct -> (KnowStruct,[(Prp,Prp)])
replaceEquivExtra mainVocab startKns = lfp step (startKns,[]) where
  step (kns,replRel) = case equivExtraVocabOf mainVocab kns of
               []        -> (kns,replRel)
               ((p,q):_) -> (replaceWithIn (p,q) kns, (p,q):replRel)

withoutProps :: [Prp] -> KnowStruct -> KnowStruct
withoutProps propsToDel (KnS oldProps oldLawBdd oldObs) =
  KnS
    (oldProps \\ propsToDel)
    (existsSet (map fromEnum propsToDel) oldLawBdd)
    [(i,os \\ propsToDel) | (i,os) <- oldObs]

instance Optimizable KnowStruct where
  optimize myVocab oldKns = newKns where
    intermediateKns = withoutProps (determinedVocabOf oldKns \\ myVocab) oldKns
    newKns = fst $ replaceEquivExtra myVocab intermediateKns

instance Optimizable KnowScene where
  optimize myVocab (oldKns,oldState) = (newKns,newState) where
    intermediateKns = withoutProps (determinedVocabOf oldKns \\ myVocab) oldKns
    removedProps = vocabOf oldKns \\ vocabOf intermediateKns
    intermediateState = oldState \\ removedProps
    (newKns,replRel) = replaceEquivExtra myVocab intermediateKns
    newState = sort $ (intermediateState \\ map fst replRel) ++ [ q | (p,q) <- replRel, p `elem` intermediateState ]

instance Optimizable MultipointedKnowScene where
  optimize myVocab (oldKns,oldStatesBdd) = (newKns,newStatesBdd) where
    intermediateKns = withoutProps (determinedVocabOf oldKns \\ myVocab) oldKns
    removedProps = vocabOf oldKns \\ vocabOf intermediateKns
    intermediateStatesBdd = existsSet (map fromEnum removedProps) oldStatesBdd
    (newKns,replRel) = replaceEquivExtra myVocab intermediateKns
    newStatesBdd = foldr (uncurry Data.HasCacBDD.substit) intermediateStatesBdd [ (fromEnum p, var (fromEnum q)) | (p,q) <-replRel ]

generatedSubstructure :: MultipointedKnowScene -> MultipointedKnowScene
generatedSubstructure kns@(KnS props oldLaw obs, curBdd) = (KnS props newLaw obs, curBdd) where
  extend this = disSet (this : [ existsSet (map fromEnum $ props \\ obs ! i) this | i <- agentsOf kns ])
  reachable = lfp extend curBdd
  newLaw = oldLaw `con` reachable

type Propulation = Tagged Quadrupel Bdd

($$) :: Monad m => ([a] -> b) -> [m a] -> m b
($$) f xs = f <$> sequence xs

checkPropu :: Propulation -> KnowStruct -> KnowStruct -> [Prp] -> Bool
checkPropu propu kns1@(KnS _ law1 obs1) kns2@(KnS _ law2 obs2) voc =
  pure top == (imp <$> lhs <*> rhs) where
    lhs = conSet $$ [mv law1, cp law2, propu]
    rhs = conSet $$ [propAgree, forth, back]
    propAgree = allsamebdd voc
    forth = conSet $$ [ forallSet (nonObs i obs1) <$>
                          (imp <$> mv law1 <*> (existsSet (nonObs i obs2) <$> (con <$> cp law2 <*> propu)))
                      | i <- agentsOf kns1 ]
    back  = conSet $$ [ forallSet (nonObs i obs1) <$>
                          (imp <$> mv law2 <*> (existsSet (nonObs i obs1) <$> (con <$> cp law1 <*> propu)))
                      | i <- agentsOf kns2 ]
    nonObs i obs = map (\(P n) -> n) $ voc \\ obs ! i


data KnowTransformer = KnTrf
  [Prp]            -- addProps
  Form             -- addLaw
  [(Prp,Bdd)]      -- changeLaw
  [(Agent,[Prp])]  -- addObs
  deriving (Eq,Show)

noChange :: ([Prp] -> Form -> [(Prp,Bdd)] -> [(Agent,[Prp])] -> KnowTransformer)
          -> [Prp] -> Form                -> [(Agent,[Prp])] -> KnowTransformer
noChange kntrf addprops addlaw = kntrf addprops addlaw []

instance HasAgents KnowTransformer where
  agentsOf (KnTrf _ _ _ obdds) = map fst obdds

instance HasPrecondition KnowTransformer where
  preOf _ = Top

instance Pointed KnowTransformer State
type Event = (KnowTransformer,State)

instance HasPrecondition Event where
  preOf (KnTrf addprops addlaw _ _, x) = simplify $ substitOutOf x addprops addlaw

instance Pointed KnowTransformer Bdd
type MultipointedEvent = (KnowTransformer,Bdd)

instance HasPrecondition MultipointedEvent where
  preOf (KnTrf addprops addlaw _ _, xsBdd) =
    simplify $ Exists addprops (Conj [ formOf xsBdd, addlaw ])

publicAnnounce :: [Agent] -> Form -> Event
publicAnnounce agents f = (noChange KnTrf [] f myobs, []) where
  myobs = [ (i,[]) | i <- agents ]

-- | shift addprops to ensure that props and newprops are disjoint:
shiftPrepare :: KnowStruct -> KnowTransformer -> (KnowTransformer, [(Prp,Prp)])
shiftPrepare (KnS props _ _) (KnTrf addprops addlaw changelaw eventObs) =
  (KnTrf shiftaddprops addlawShifted changelawShifted eventObsShifted, shiftrel) where
    shiftrel = sort $ zip addprops [(freshp props)..]
    shiftaddprops = map snd shiftrel
    -- apply the shifting to addlaw, changelaw and eventObs:
    addlawShifted    = replPsInF shiftrel addlaw
    changelawShifted = map (second (relabelWith shiftrel)) changelaw
    eventObsShifted  = map (second (map (apply shiftrel))) eventObs

instance Update KnowScene Event where
  unsafeUpdate (kns@(KnS props _ _),s) (ctrf, eventFactsUnshifted) = (KnS newprops newlaw newobs, news) where
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    (KnTrf addprops _ changelaw _, shiftrel) = shiftPrepare kns ctrf
    -- the actual event:
    eventFacts = map (apply shiftrel) eventFactsUnshifted
    -- PART 2: COPYING the modified propositions
    changeprops = map fst changelaw
    copyrel = zip changeprops [(freshp $ props ++ addprops)..]
    -- do the pointless update and calculate new actual state
    KnS newprops newlaw newobs = unsafeUpdate kns ctrf
    news = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , eventFacts
            , filter (\ p -> bddEval (s ++ eventFacts) (changelaw ! p)) changeprops ]

instance Update KnowStruct KnowTransformer where
  checks = [haveSameAgents]
  unsafeUpdate kns ctrf = KnS newprops newlaw newobs where
    (KnS newprops newlaw newobs, _) = unsafeUpdate (kns,undefined::Bdd) (ctrf,undefined::Bdd) -- using laziness!

instance Update MultipointedKnowScene MultipointedEvent where
  unsafeUpdate (kns@(KnS props law obs),statesBdd) (ctrf,eventsBddUnshifted)  =
    (KnS newprops newlaw newobs, newStatesBDD) where
      (KnTrf addprops addlaw changelaw eventObs, shiftrel) = shiftPrepare kns ctrf
      -- apply the shifting to eventsBdd:
      eventsBdd = relabelWith shiftrel eventsBddUnshifted
      -- PART 2: COPYING the modified propositions
      changeprops = map fst changelaw
      copyrel = zip changeprops [(freshp $ props ++ addprops)..]
      copychangeprops = map snd copyrel
      newprops = sort $ props ++ addprops ++ copychangeprops -- V u V^+ u V^o
      newlaw = conSet $ relabelWith copyrel (con law (bddOf kns addlaw))
                      : [var (fromEnum q) `equ` relabelWith copyrel (changelaw ! q) | q <- changeprops]
      newobs = [ (i , sort $ map (applyPartial copyrel) (obs ! i) ++ eventObs ! i) | i <- map fst obs ]
      newStatesBDD = conSet [ relabelWith copyrel statesBdd, eventsBdd ]

texBddWith :: (Int -> String) -> Bdd -> String
texBddWith myShow b = unsafePerformIO $ do
  haveDot2tex <- findExecutable "dot2tex"
  case haveDot2tex of
    Nothing -> error "Please install dot2tex which is needed to show BDDs."
    Just d2t -> do
      (i,o,_,_) <- runInteractiveCommand $ d2t ++ " --figpreamble=\"\\huge\" --figonly -traw"
      hPutStr i (genGraphWith myShow b ++ "\n")
      hClose i
      result <- hGetContents o
      return $ dropWhileEnd isSpace $ dropWhile isSpace result

texBDD :: Bdd -> String
texBDD = texBddWith show

newtype WrapBdd = Wrap Bdd

instance TexAble WrapBdd where
  tex (Wrap b) = texBDD b

instance TexAble KnowStruct where
  tex (KnS props lawbdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD lawbdd
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]

instance TexAble KnowScene where
  tex (kns, state) = tex kns ++ " , " ++ tex state

instance TexAble MultipointedKnowScene where
  tex (kns, statesBdd) = concat
    [ " \\left( \n"
    , tex kns ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD statesBdd
    , "} \\end{array}\n "
    , " \\right)" ]

instance TexAble KnowTransformer where
  tex (KnTrf addprops addlaw changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", \\ "
    , tex addlaw, ", \\ "
    , intercalate ", " $ map texChange changelaw
    , ", \\ \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) eventObs)
    , "\\end{array}\n"
    , " \\right) \n"
    ] where
        texChange (prop,changebdd) = concat
          [ tex prop ++ " := "
          , " \\begin{array}{l} \\scalebox{0.4}{"
          , texBDD changebdd
          , "} \\end{array}\n " ]

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", \\ ", tex eventFacts, " \\right) \n" ]

instance TexAble MultipointedEvent where
  tex (trf, eventsBdd) = concat
    [ " \\left( \n"
    , tex trf ++ ", \\ "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD eventsBdd
    , "} \\end{array}\n "
    , " \\right)" ]

reduce :: Event -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = pure $ Neg (preOf e)
reduce e (PrpF p)     = Impl (preOf e) <$> Just (PrpF p) -- FIXME use change!
reduce e (Neg f)      = Impl (preOf e) <$> (Neg <$> reduce e f)
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (preOf e) <$> (Xor <$> mapM (reduce e) fs)
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce event@(trf@(KnTrf addprops _ _ obs), x) (K a f) =
  Impl (preOf event) <$> (Conj <$> sequence
    [ K a <$> reduce (trf,y) f | y <- powerset addprops
                               , (x `intersect` (obs ! a)) `seteq` (y `intersect` (obs ! a))
    ])
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ PubAnnounceW {} = Nothing
reduce _ Announce     {} = Nothing
reduce _ AnnounceW    {} = Nothing
reduce _ Dia          {} = Nothing

instance Arbitrary KnowStruct where
  arbitrary = do
    numExtraVars <- choose (0,2)
    let myVocabulary = defaultVocabulary ++ take numExtraVars [freshp defaultVocabulary ..]
    (BF statelaw) <- sized (randomboolformWith myVocabulary) `suchThat` (\(BF bf) -> boolBddOf bf /= bot)
    obs <- mapM (\i -> do
      obsVars <- sublistOf myVocabulary
      return (i,obsVars)
      ) defaultAgents
    return $ KnS myVocabulary (boolBddOf statelaw) obs
  shrink kns = [ withoutProps [p] kns | length (vocabOf kns) > 1, p <- vocabOf kns \\ defaultVocabulary ]
