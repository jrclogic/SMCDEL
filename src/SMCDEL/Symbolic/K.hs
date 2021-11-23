{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

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
import SMCDEL.Symbolic.S5 (State,texBDD,boolBddOf,texBddWith,bddEval,relabelWith)
import SMCDEL.Translations.S5 (booloutof)

mvP, cpP :: Prp -> Prp
mvP (P n) = P  (2*n)      -- represent p  in the double vocabulary
cpP (P n) = P ((2*n) + 1) -- represent p' in the double vocabulary

-- | Map p or p' in double vocabulary to p in single vocabulary.
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

cpBdd :: Bdd -> RelBDD
cpBdd b = Tagged $ relabelFun (\n -> (2*n) + 1) b

mvBdd :: Bdd -> RelBDD
mvBdd b = Tagged $ relabelFun (2 *) b

unmvBdd :: RelBDD -> Bdd
unmvBdd (Tagged b) =
  relabelFun (\n -> if even n then n `div` 2 else error ("Not even: " ++ show n ++ "in the RelBDD " ++ show b)) b

propRel2bdd :: [Prp] -> M.Map State [State] -> RelBDD
propRel2bdd props relation = pure $ disSet (M.elems $ M.mapWithKey linkbdd relation) where
  linkbdd here theres =
    con (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there <- theres ] )

samplerel ::  M.Map State [State]
samplerel = M.fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]

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

data BelStruct = BlS [Prp]              -- vocabulary
                     Bdd                -- state law
                     (M.Map Agent RelBDD) -- observation laws
                  deriving (Eq,Show)

instance Pointed BelStruct State
type BelScene = (BelStruct,State)

instance Pointed BelStruct Bdd
type MultipointedBelScene = (BelStruct,Bdd)

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ obdds) = M.keys obdds

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

bddOf bls@(BlS allprops lawbdd obdds) (K i form) = unmvBdd result where
  result = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls form)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf bls@(BlS allprops lawbdd obdds) (Kw i form) = unmvBdd result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf bls f)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf bls@(BlS voc lawbdd obdds) (Ck ags form) = lfp lambda top where
  ps' = map fromEnum $ cp voc
  lambda :: Bdd -> Bdd
  lambda z = unmvBdd $
    forallSet ps' <$>
      (imp <$> cpBdd lawbdd <*>
        (imp <$> (disSet <$> sequence [obdds ! i | i <- ags]) <*>
          cpBdd (con (bddOf bls form) z)))

bddOf bls (Ckw ags form) = dis (bddOf bls (Ck ags form)) (bddOf bls (Ck ags (Neg form)))

bddOf bls (PubAnnounce f g) =
  imp (bddOf bls f) (bddOf (bls `update` f) g)
bddOf bls (PubAnnounceW f g) =
  ifthenelse (bddOf bls f)
    (bddOf (bls `update`     f) g)
    (bddOf (bls `update` Neg f) g)

bddOf bls@(BlS props _ _) (Announce ags f g) =
  imp (bddOf bls f) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce bls ags f) g
    (P k) = freshp props

bddOf bls@(BlS props _ _) (AnnounceW ags f g) =
  ifthenelse (bddOf bls f) bdd2a bdd2b where
    bdd2a = restrict (bddOf (announce bls ags f      ) g) (k,True)
    bdd2b = restrict (bddOf (announce bls ags (Neg f)) g) (k,True)
    (P k) = freshp props

bddOf bls (Dia (Dyn dynLabel d) f) =
    con (bddOf bls preCon)                    -- 5. Prefix with "precon AND ..." (diamond!)
    . relabelWith copyrelInverse              -- 4. Copy back changeProps V_-^o to V_-
    . simulateActualEvents                    -- 3. Simulate actual event(s) [see below]
    . substitSimul [ (k, changeLaw ! p)       -- 2. Replace changeProps V_- with postcons
                   | p@(P k) <- changeProps]  --    (no "relabelWith copyrel", undone in 4)
    . bddOf (bls `update` trf)                -- 1. boolean equivalent wrt new struct
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

validViaBdd :: BelStruct -> Form -> Bool
validViaBdd bls@(BlS _ lawbdd _) f = top == imp lawbdd (bddOf bls f)

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

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS props lawbdd obdds) ags psi = BlS newprops newlawbdd newobdds where
  (P k)     = freshp props
  newprops  = sort $ P k : props
  newlawbdd = con lawbdd (imp (var k) (bddOf bls psi))
  newobdds  = M.mapWithKey newOfor obdds
  newOfor i oi | i `elem` ags = con <$> oi <*> (equ <$> mvBdd (var k) <*> cpBdd (var k))
               | otherwise    = con <$> oi <*> (neg <$> cpBdd (var k)) -- p_psi'

statesOf :: BelStruct -> [State]
statesOf (BlS allprops lawbdd _) = map (sort.getTrues) prpsats where
  bddvars = map fromEnum allprops
  bddsats = allSatsWith bddvars lawbdd
  prpsats = map (map (first toEnum)) bddsats
  getTrues = map fst . filter snd

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
    [ " \\left( \n"
    , tex props, ", "
    , bddprefix, texBDD lawbdd, bddsuffix
    , ", "
    , intercalate ", " obddstrings
    , " \\right) \n"
    ] where
        obddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (M.toList obdds)
        bddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble BelScene where
  tex (bls, state) = concat
    [ " \\left( \n", tex bls, ", ", tex state, " \\right) \n" ]

instance TexAble MultipointedBelScene where
  tex (bls, statesBdd) = concat
    [ " \\left( \n"
    , tex bls ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD statesBdd
    , "} \\end{array}\n "
    , " \\right)" ]

cleanupObsLaw :: BelScene -> BelScene
cleanupObsLaw (BlS vocab law obs, s) = (BlS vocab law (M.map clean obs), s) where
  clean relbdd = restrictLaw <$> relbdd <*> (con <$> cpBdd law <*> mvBdd law)

determinedVocabOf :: BelStruct -> [Prp]
determinedVocabOf strct = filter (\p -> validViaBdd strct (PrpF p) || validViaBdd strct (Neg $ PrpF p)) (vocabOf strct)

nonobsVocabOf  :: BelStruct -> [Prp]
nonobsVocabOf (BlS vocab _law obs) = filter (`notElem` usedVars) vocab where
  usedVars =
    map unmvcpP
    $ sort
    $ nub
    $ concatMap (map P . Data.HasCacBDD.allVarsOf . untag)
    $ M.elems obs

withoutProps :: [Prp] -> BelStruct -> BelStruct
withoutProps propsToDel (BlS oldProps oldLawBdd oldObs) =
  BlS
    (oldProps \\ propsToDel)
    (existsSet (map fromEnum propsToDel) oldLawBdd)
    (M.map (fmap $ existsSet (map fromEnum propsToDel)) oldObs)

equivExtraVocabOf :: [Prp] -> BelStruct -> [(Prp,Prp)]
equivExtraVocabOf mainVocab bls =
  [ (p,q) | p <- vocabOf bls \\ mainVocab, q <- vocabOf bls, p > q, validViaBdd bls (PrpF p `Equi` PrpF q) ]

replaceWithIn :: (Prp,Prp) -> BelStruct -> BelStruct
replaceWithIn (p,q) (BlS oldProps oldLaw oldObs) =
  BlS (delete p oldProps) (changeBdd oldLaw) (fmap (fmap changeRelBdd) oldObs) where
  changeBdd    = Data.HasCacBDD.relabel [ (fromEnum p, fromEnum q) ]
  changeRelBdd = Data.HasCacBDD.relabel $ sort [ (fromEnum $ mvP p, fromEnum $ mvP q)
                                               , (fromEnum $ cpP p, fromEnum $ cpP q) ]

replaceEquivExtra :: [Prp] -> BelStruct -> (BelStruct,[(Prp,Prp)])
replaceEquivExtra mainVocab startBls = lfp step (startBls,[]) where
  step (bls,replRel) = case equivExtraVocabOf mainVocab bls of
               []        -> (bls,replRel)
               ((p,q):_) -> (replaceWithIn (p,q) bls, (p,q):replRel)

instance Optimizable BelStruct where
  optimize myVocab bls = fst $ replaceEquivExtra myVocab $
    withoutProps ((determinedVocabOf bls `intersect` nonobsVocabOf bls) \\ myVocab) bls

instance Optimizable MultipointedBelScene where
  optimize myVocab (oldBls,oldStatesBdd) = (newKns,newStatesBdd) where
    intermediateBls = withoutProps ((determinedVocabOf oldBls `intersect` nonobsVocabOf oldBls) \\ myVocab) oldBls
    removedProps = vocabOf oldBls \\ vocabOf intermediateBls
    intermediateStatesBdd = existsSet (map fromEnum removedProps) oldStatesBdd
    (newKns,replRel) = replaceEquivExtra myVocab intermediateBls
    newStatesBdd = Data.HasCacBDD.relabel [ (fromEnum p, fromEnum q) | (p,q) <-replRel ] intermediateStatesBdd

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

data Transformer = Trf
  [Prp] -- addprops
  Form  -- event law
  (M.Map Prp Bdd) -- changelaw
  (M.Map Agent RelBDD) -- eventObs
  deriving (Eq,Show)

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

instance TexAble Transformer where
  tex (Trf addprops addlaw changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", "
    , tex addlaw, ", "
    , tex changeprops, ", "
    , intercalate ", " $ map snd . M.toList $ M.mapWithKey texChange changelaw, ", "
    , intercalate ", " eobddstrings
    , " \\right) \n"
    ] where
        changeprops = M.keys changelaw
        texChange prop changebdd = tex prop ++ " := " ++ tex (formOf changebdd)
        eobddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (M.toList eventObs)
        bddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", ", tex eventFacts, " \\right) \n" ]

instance TexAble MultipointedEvent where
  tex (trf, eventStates) = concat
    [ " \\left( \n"
    , tex trf ++ ", \\ "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD eventStates
    , "} \\end{array}\n "
    , " \\right)" ]

-- | shift addprops to ensure that props and newprops are disjoint:
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
    newobs = M.mapWithKey (\i oldobs -> con <$> (relabelWith copyrelMVCP <$> oldobs) <*> (addObs ! i)) obdds
    news = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , eventFacts
            , filter (\ p -> bddEval (s ++ eventFacts) (changelaw ! p)) changeprops ]

instance Update BelStruct Transformer where
  checks = [haveSameAgents]
  unsafeUpdate bls ctrf = BlS newprops newlaw newobs where
    (BlS newprops newlaw newobs, _) = unsafeUpdate (bls,undefined::State) (ctrf,undefined::State) -- using laziness!

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

trfPost :: Event -> Prp -> Bdd
trfPost (Trf addprops _ changelaw _, x) p
  | p `elem` M.keys changelaw = restrictLaw (changelaw ! p) (booloutof x addprops)
  | otherwise                 = boolBddOf $ PrpF p

reduce :: Event -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = Just $ Neg $ preOf e
reduce e (PrpF p)     = Impl (preOf e) <$> Just (formOf $ trfPost e p)
reduce e (Neg f)      = Impl (preOf e) <$> (Neg <$> reduce e f)
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (preOf e) <$> (Xor <$> mapM (reduce e) fs)
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce e@(t@(Trf addprops _ _ eventObs), x) (K a f) =
  Impl (preOf e) <$> (Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME is this a bit much?
                             , tagBddEval (mv x ++ cp y) (eventObs ! a)
    ])
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ PubAnnounceW {} = Nothing
reduce _ Announce     {} = Nothing
reduce _ AnnounceW    {} = Nothing
reduce _ Dia          {} = Nothing

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

evalViaBddReduce :: BelScene -> Event -> Form -> Bool
evalViaBddReduce (bls,s) event f = evaluateFun (bddReduce (bls,s) event f) (\n -> P n `elem` s)
