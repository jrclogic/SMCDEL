{-# LANGUAGE FlexibleInstances, InstanceSigs, MultiParamTypeClasses, ScopedTypeVariables, FlexibleContexts #-}

module SMCDEL.Symbolic.K_CUDD where

import Data.Bifunctor
import Data.Tagged

import Control.Arrow (Arrow ((&&&)))
import SMCDEL.Internal.MyHaskCUDD
import Data.List (sort,intersect,(\\), intercalate)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

import SMCDEL.Explicit.K
import SMCDEL.Internal.Help (apply,lfp,powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5_CUDD (KnState,boolDdOf, boolDDoutof, ddToForm, ddEval, evalAssDD, texDd, texDdFun)
import Cudd.Cudd ( DdManager )

mvP, cpP :: Prp -> Prp
mvP (P n) = P  (2*n)      -- represent p  in the double vocabulary
cpP (P n) = P ((2*n) + 1) -- represent p' in the double vocabulary

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
type RelDD a b c = Tagged Dubbel (Dd a b c)

totalRelDd, emptyRelDd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> RelDD a b c
totalRelDd mgr = pure $ boolDdOf mgr Top
emptyRelDd mgr = pure $ boolDdOf mgr Bot

allsamedd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> RelDD a b c
allsamedd mgr ps = pure $ conSet mgr [boolDdOf mgr $ PrpF p `Equi` PrpF p' | (p,p') <- zip (mv ps) (cp ps)]

class TagDd t a b c where
  tagDdEval :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> Tagged t (Dd a b c) -> Bool
  tagDdEval mgr truths querydd = evalAssDD mgr (untag querydd) (\n -> P n `elem` truths)

instance TagDd Dubbel a b c

cpDd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> Dd a b c -> RelDD a b c
cpDd mgr vocab b = Tagged $ relabelWith mgr (zipWith (curry (bimap fromEnum fromEnum)) vocab (map cpP vocab)) b

mvDd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> Dd a b c -> RelDD a b c
mvDd mgr vocab b = Tagged $ relabelWith mgr (zipWith (curry (bimap fromEnum fromEnum)) vocab (map mvP vocab)) b

unmvDd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> RelDD a b c -> Dd a b c
unmvDd mgr vocab (Tagged b) = relabelWith mgr (zipWith (curry (bimap fromEnum fromEnum)) (map mvP vocab) vocab) b

propRel2dd :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> M.Map KnState [KnState] -> RelDD a b c
propRel2dd mgr props relation = pure $ disSet mgr (M.elems $ M.mapWithKey linkdd relation) where
  linkdd here theres =
    con mgr (boolDDoutof mgr (mv here) (mv props))
        (disSet mgr [ boolDDoutof mgr (cp there) (cp props) | there <- theres ] )

samplerel ::  M.Map KnState [KnState]
samplerel = M.fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]

relDdOfIn :: (DdCtx a b c) => Cudd.Cudd.DdManager -> Agent -> KripkeModel -> RelDD a b c
relDdOfIn mgr i (KrM m)
  | not (distinctVal (KrM m)) = error "m does not have distinct valuations."
  | otherwise = pure $ disSet mgr (M.elems $ M.map linkdd m) where
    linkdd (mapPropBool,mapAgentReach)  =
      con mgr
        (boolDDoutof mgr (mv here) (mv props))
        (disSet mgr [ boolDDoutof mgr (cp there) (cp props) | there<-theres ] )
      where
        props = M.keys mapPropBool
        here = M.keys (M.filter id mapPropBool)
        theres = map (truthsInAt (KrM m)) (mapAgentReach ! i)

data BelStruct a b c = BlS Cudd.Cudd.DdManager  -- Cudd manager for removing/reseting variables
                     [Prp]                -- vocabulary
                     (Dd a b c)               -- state law
                     (M.Map Agent (RelDD a b c)) -- observation laws
                  deriving (Eq,Show)

instance Pointed (BelStruct a b c) KnState
type BelScene a b c = (BelStruct a b c,KnState)

instance Pointed (BelStruct a b c) (Dd a b c)
type MultipointedBelScene a b c = (BelStruct a b c, Dd a b c)

instance HasVocab (BelStruct a b c) where
  vocabOf (BlS _ voc _ _) = voc

instance HasAgents (BelStruct a b c) where
  agentsOf (BlS _ _ _ odds) = M.keys odds

ddOf :: (DdCtx a b c) => BelStruct a b c -> Form -> Dd a b c
ddOf (BlS mgr _ _ _)   Top           = top mgr
ddOf (BlS mgr _ _ _)   Bot           = bot mgr
ddOf (BlS mgr _ _ _)   (PrpF (P n))  = var mgr n
ddOf bls@(BlS mgr _ _ _) (Neg form)    = neg mgr $ ddOf bls form
ddOf bls@(BlS mgr _ _ _) (Conj forms)  = conSet mgr $ map (ddOf bls) forms
ddOf bls@(BlS mgr _ _ _) (Disj forms)  = disSet mgr $ map (ddOf bls) forms
ddOf bls@(BlS mgr _ _ _) (Xor  forms)  = xorSet mgr $ map (ddOf bls) forms
ddOf bls@(BlS mgr _ _ _) (Impl f g)    = imp mgr (ddOf bls f) (ddOf bls g)
ddOf bls@(BlS mgr _ _ _) (Equi f g)    = equ mgr (ddOf bls f) (ddOf bls g)
ddOf bls@(BlS mgr _ _ _) (Forall ps f) = forallSet mgr (map fromEnum ps) (ddOf bls f)
ddOf bls@(BlS mgr _ _ _) (Exists ps f) = existsSet mgr (map fromEnum ps) (ddOf bls f)

ddOf bls@(BlS mgr allprops lawdd odds) (K i form) = unmvDd mgr allprops result
  where
  result = forallSet mgr ps' <$> (imp mgr <$> cpDd mgr allprops lawdd <*> (imp mgr <$> omegai <*> cpDd mgr allprops (ddOf bls form)))
  ps'    = map fromEnum $ cp allprops
  omegai = odds ! i

ddOf bls@(BlS mgr allprops lawdd odds) (Kw i form) = unmvDd mgr allprops result
  where
  result = dis mgr <$> part form <*> part (Neg form)
  part f = forallSet mgr ps' <$> (imp mgr <$> cpDd mgr allprops lawdd <*> (imp mgr <$> omegai <*> cpDd mgr allprops (ddOf bls f)))
  ps'    = map fromEnum $ cp allprops
  omegai = odds ! i

ddOf bls@(BlS mgr voc (lawdd :: Dd a b c) odds) (Ck ags form) = lfp lambda (top mgr)  where
  ps' = map fromEnum $ cp voc
  lambda :: Dd a b c -> Dd a b c
  lambda z = unmvDd mgr voc $
    forallSet mgr ps' <$>
      (imp mgr <$> cpDd mgr voc lawdd <*>
        (imp mgr <$> (disSet mgr <$> sequence [odds ! i | i <- ags]) <*>
          cpDd mgr voc (con mgr (ddOf bls form) z)))

ddOf bls@(BlS mgr _ _ _) (Ckw ags form) = dis mgr (ddOf bls (Ck ags form)) (ddOf bls (Ck ags (Neg form)))

ddOf bls@(BlS mgr _ _ _) (PubAnnounce f g) =
  imp mgr (ddOf bls f) (ddOf  (pubAnnounce bls f) g)
ddOf bls@(BlS mgr _ _ _) (PubAnnounceW f g) =
  ifthenelse mgr (ddOf bls f)
    (ddOf  (pubAnnounce bls f      ) g)
    (ddOf  (pubAnnounce bls (Neg f)) g)

ddOf bls@(BlS mgr props law obs) (Announce ags f g) =
  imp mgr (ddOf bls f) (restrict mgr dd2 (k,True)) where
    dd2  = ddOf (announce (BlS mgr props law obs) ags f) g
    (P k) = freshp props

ddOf bls@(BlS mgr props law obs) (AnnounceW ags f g) =
  ifthenelse mgr (ddOf bls f) dd2a dd2b where
    dd2a = restrict mgr (ddOf  (announce (BlS mgr props law obs) ags f      ) g) (k,True)
    dd2b = restrict mgr (ddOf  (announce (BlS mgr props law obs) ags (Neg f)) g) (k,True)
    (P k) = freshp props

ddOf _ (Dia _ _) = error "Dynamic operators are not implemented in K_CUDD."

validViaDd :: (DdCtx a b c) => BelStruct a b c -> Form -> Bool
validViaDd bls@(BlS mgr _ lawdd _) f = top mgr == imp mgr lawdd (ddOf bls f)

evalViaDd :: (DdCtx a b c) => BelScene a b c -> Form -> Bool
evalViaDd (bls@(BlS mgr allprops _ _),s) f = let
    dd  = ddOf bls f
    b    = restrictSet mgr dd list
    list = [ (n, P n `elem` s) | (P n) <- allprops ]
  in
    case (b==top mgr,b==bot mgr) of
      (True,_) -> True
      (_,True) -> False
      _        -> error $ "evalViaDd failed: Composite DD leftover!\n"
        ++ "  bls:  " ++ show bls ++ "\n"
        ++ "  s:    " ++ show s ++ "\n"
        ++ "  form: " ++ show f ++ "\n"
        ++ "  dd:  " ++ show dd ++ "\n"
        ++ "  list: " ++ show list ++ "\n"
        ++ "  b:    " ++ show b ++ "\n"

instance (DdCtx a b c) => Semantics (BelStruct a b c) where
  isTrue = validViaDd

instance (DdCtx a b c) => Semantics (BelScene a b c) where
  isTrue = evalViaDd

instance (DdCtx a b c) => Semantics (MultipointedBelScene a b c) where
  isTrue (kns@(BlS mgr _ lawBdd _), statesBdd) f =
    let a = imp mgr lawBdd (imp mgr statesBdd (ddOf kns f))
     in a == top mgr

instance (DdCtx a b c) => Update (BelStruct a b c) Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate bls@(BlS mgr allprops lawdd obs) f =
    BlS mgr allprops (con mgr lawdd (ddOf bls f)) obs

instance (DdCtx a b c) => Update (BelScene a b c) Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi,s)

pubAnnounce :: (DdCtx a b c) => BelStruct a b c -> Form -> BelStruct a b c
pubAnnounce bls@(BlS mgr allprops lawdd obs) f =
  BlS mgr allprops (con mgr lawdd (ddOf bls f)) obs

announce :: (DdCtx a b c) => BelStruct a b c -> [Agent] -> Form -> BelStruct a b c
announce bls@(BlS mgr props lawdd odds) ags psi = BlS mgr newprops newlawdd newodds where
  (P k)     = freshp props
  newprops  = sort $ P k : props
  newlawdd = con mgr lawdd (imp mgr (var mgr k) (ddOf  bls psi))
  newodds  = M.mapWithKey newOfor odds
  newOfor i oi | i `elem` ags = con mgr <$> oi <*> (equ mgr <$> mvDd mgr newprops (var mgr k) <*> cpDd mgr newprops (var mgr k))
               | otherwise    = con mgr <$> oi <*> (neg mgr <$> cpDd mgr newprops (var mgr k)) -- p_psi'

whereViaDd :: (DdCtx a b c) => BelStruct a b c -> Form -> [KnState]
whereViaDd kns f = statesOf (kns `update` f)

-- | Get all states of a belief structure - slow version using restrict.
-- A faster version would need an efficient `allSats` which is not available for ZDDs.
statesOf :: DdCtx a b c => BelStruct a b c -> [KnState]
statesOf (BlS mgr allprops lawdd _) = loop allprops lawdd where
  loop [] _ = []
  loop v d = r v d True ++ r v d False
  r ((P n):ns) d b
    | restrict mgr d (n,b) == bot mgr = []
    | restrict mgr d (n,b) == top mgr = if b then map ([P n] ++) (powerset ns) else powerset ns
    | otherwise =
      if b then map ([P n] ++) $ loop ns (restrict mgr d (n,b)) else loop ns (restrict mgr d (n,b))
  r [] _ _ = error "impossible?"

-- | Faster statesOf, for BDDs only.
statesOfFast :: BelStruct B O1 I1 -> [KnState]
statesOfFast (BlS mgr allprops lawdd _) = map (sort.getTrues) prpsats where
  ddvars = map fromEnum allprops
  ddsats = allSatsWith mgr ddvars lawdd
  prpsats = map (map (first toEnum)) ddsats
  getTrues = map fst . filter snd

-- * Visualisation

texRelDD :: DdCtx a b c => Cudd.Cudd.DdManager -> RelDD a b c -> String
texRelDD mgr (Tagged b) = texDdFun mgr b texRelProp where
  texRelProp n
    | even n    = show (n `div` 2)
    | otherwise = show ((n - 1) `div` 2) ++ "'"

ddprefix, ddsuffix :: String
ddprefix = "\\begin{array}{l} \\scalebox{0.3}{"
ddsuffix = "} \\end{array} \n"

instance DdCtx a b c => TexAble (BelStruct a b c) where
  tex (BlS mgr props lawdd odds) = concat
    [ " \\left( \n"
    , tex props, ", "
    , ddprefix, texDd mgr lawdd, ddsuffix
    , ", "
    , intercalate ", " oddstrings
    , " \\right) \n"
    ] where
        oddstrings = map (ddstring . (fst &&& (texRelDD mgr . snd))) (M.toList odds)
        ddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ ddprefix ++ os ++ ddsuffix

instance DdCtx a b c => TexAble (BelScene a b c) where
  tex (bls, state) = concat
    [ " \\left( \n", tex bls, ", ", tex state, " \\right) \n" ]

instance DdCtx a b c => TexAble (MultipointedBelScene a b c) where
  tex (bls@(BlS mgr _ _ _), statesDd) = concat
    [ " \\left( \n"
    , tex bls ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDd mgr statesDd
    , "} \\end{array}\n "
    , " \\right)" ]

cleanupObsLaw :: (DdCtx a b c) => BelScene a b c -> BelScene a b c
cleanupObsLaw (BlS mgr vocab law obs, s) = (BlS mgr vocab law (M.map clean obs), s) where
  clean reldd = restrictLaw mgr (map fromEnum vocab) <$> reldd <*> (con mgr <$> cpDd mgr vocab law <*> mvDd mgr vocab law)

determinedVocabOf :: (DdCtx a b c) => BelStruct a b c -> [Prp]
determinedVocabOf strct = filter (\p -> validViaDd strct (PrpF p) || validViaDd strct (Neg $ PrpF p)) (vocabOf strct)

nonobsVocabOf  :: (DdCtx a b c) => BelStruct a b c -> [Prp]
nonobsVocabOf (BlS mgr vocab _law obs) = filter (`notElem` usedVars) vocab where
  usedVars =
    map unmvcpP
    $ sort
    $ concatMap (map P . getDependentVars mgr (map fromEnum vocab) . untag . snd)
    $ M.toList obs

withoutProps :: (DdCtx a b c) => [Prp] -> BelStruct a b c -> BelStruct a b c
withoutProps propsToDel (BlS mgr oldProps oldLawDd oldObs) =
  BlS
    mgr
    (oldProps \\ propsToDel)
    (existsSet mgr (map fromEnum propsToDel) oldLawDd)
    (M.map (fmap $ existsSet mgr (map fromEnum propsToDel)) oldObs)

data Transformer a b c = Trf
  Cudd.Cudd.DdManager -- Cudd manager needed for reseting/removing variables
  [Prp] -- addprops
  Form  -- event law
  (M.Map Prp (Dd a b c)) -- changelaw
  (M.Map Agent (RelDD a b c)) -- eventObs
  deriving (Eq,Show)

instance HasAgents (Transformer a b c) where
  agentsOf (Trf _ _ _ _ odds) = M.keys odds

instance HasPrecondition (Transformer a b c) where
  preOf _ = Top

instance Pointed (Transformer a b c) KnState
type Event a b c = (Transformer a b c,KnState)

instance HasPrecondition (Event a b c) where
  preOf (Trf _ addprops addlaw _ _, x) = simplify $ substitOutOf x addprops addlaw

instance Pointed (Transformer a b c) (Dd a b c)
type MultipointedEvent a b c = (Transformer a b c, Dd a b c)

instance (DdCtx a b c) => HasPrecondition (MultipointedEvent a b c) where
  preOf (Trf mgr addprops addlaw _ _, xsDd) =
    simplify $ Exists addprops (Conj [ ddToForm mgr addprops xsDd, addlaw ])
    -- TODO: ddToForm should use vocab of xsDd

instance DdCtx a b c => TexAble (Transformer a b c) where
  tex (Trf mgr addprops addlaw changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", "
    , tex addlaw, ", "
    , tex changeprops, ", "
    , intercalate ", " $ map snd . M.toList $ M.mapWithKey texChange changelaw, ", "
    , intercalate ", " eoddstrings
    , " \\right) \n"
    ] where
        changeprops = M.keys changelaw
        texChange prop changedd = tex prop ++ " := " ++ tex (ddToForm mgr addprops changedd)
        eoddstrings = map (ddstring . (fst &&& (texRelDD mgr . snd))) (M.toList eventObs)
        ddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ ddprefix ++ os ++ ddsuffix

instance DdCtx a b c => TexAble (Event a b c) where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", ", tex eventFacts, " \\right) \n" ]

instance DdCtx a b c => TexAble (MultipointedEvent a b c) where
  tex :: DdCtx a b c => MultipointedEvent a b c -> String
  tex (trf@(Trf mgr _ _ _ _), eventStates) = concat
    [ " \\left( \n"
    , tex trf ++ ", \\ "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDd mgr eventStates
    , "} \\end{array}\n "
    , " \\right)" ]

-- | Shift addprops to ensure that props and newprops are disjoint.
shiftPrepare :: (DdCtx a b c) => BelStruct a b c -> Transformer a b c -> (Transformer a b c, [(Prp,Prp)])
shiftPrepare (BlS mgr props _ _) (Trf _ addprops addlaw changelaw eventObs) =
  (Trf mgr shiftaddprops addlawShifted changelawShifted eventObsShifted, shiftrel) where
    shiftrel = sort $ zip addprops [(freshp props)..]
    shiftaddprops = map snd shiftrel
    -- apply the shifting to addlaw, changelaw and eventObs:
    addlawShifted    = replPsInF shiftrel addlaw
    changelawShifted = M.map (relabelWith mgr (map (bimap fromEnum fromEnum) shiftrel)) changelaw
    -- to shift addObs we need shiftrel in the double vocabulary:
    shiftrelMVCP = sort $ zip (mv addprops) (mv shiftaddprops)
                       ++ zip (cp addprops) (cp shiftaddprops)
    eventObsShifted  = M.map (fmap $ relabelWith mgr (map (bimap fromEnum fromEnum) shiftrelMVCP)) eventObs

instance (DdCtx a b c) => Update (BelScene a b c) (Event a b c) where
  checks = [haveSameAgents, sameManager, preCheck] where
    -- Check that BelScene and Event use the same manager:
    sameManager (BlS mgr _ _ _, _) (Trf mgr' _ _ _ _ , _) = mgr == mgr'
  unsafeUpdate (bls@(BlS mgr props law odds),s) (trf, eventFactsUnshifted) = (BlS mgr newprops newlaw newobs, news) where
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    (Trf _ addprops addlaw changelaw addObs, shiftrel) = shiftPrepare bls trf
    -- the actual event:
    eventFacts = map (apply shiftrel) eventFactsUnshifted
    -- PART 2: COPYING the modified propositions
    changeprops = M.keys changelaw
    copyrel = zip changeprops [(freshp $ props ++ addprops)..]
    copychangeprops = map snd copyrel
    copyrelMVCP = map (bimap fromEnum fromEnum) $
                  sort $ zip (mv changeprops) (mv copychangeprops)
                      ++ zip (cp changeprops) (cp copychangeprops)
    -- PART 3: actual transformation
    newprops = sort $ props ++ addprops ++ copychangeprops
    copyRelInt = map (bimap fromEnum fromEnum) copyrel
    newlaw = conSet mgr $ relabelWith mgr copyRelInt (con mgr law (ddOf bls addlaw))
                    : [equ mgr (var mgr (fromEnum q)) (relabelWith mgr copyRelInt (changelaw ! q)) | q <- changeprops]
    newobs = M.mapWithKey (\i oldobs -> con mgr <$> (relabelWith mgr copyrelMVCP <$> oldobs) <*> (addObs ! i)) odds
    news = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , eventFacts
            , filter (\ p -> ddEval mgr (s ++ eventFacts) (changelaw ! p)) changeprops ]

instance (DdCtx a b c) => Update (BelStruct a b c) (Transformer a b c) where
  checks = [haveSameAgents]
  unsafeUpdate bls ctrf = BlS mgr newprops newlaw newobs where
    (BlS mgr newprops newlaw newobs, _) = unsafeUpdate (bls,undefined::KnState) (ctrf,undefined::KnState) -- using laziness!

instance (DdCtx a b c, DdTOI a O1 I1, DdTO a O1, DdTOI a b I1) => Update (BelScene a b c) (MultipointedEvent a b c) where
  checks = [haveSameAgents, sameManager, preCheck] where
    -- Check that BelScene and MultipointedEvent use the same manager:
    sameManager (BlS mgr _ _ _, _) (Trf mgr' _ _ _ _ , _) = mgr == mgr'
  unsafeUpdate ((bls,s) :: BelScene a b c) (trfUnshifted, eventFactsDdUnshifted) =
    update (bls,s) (trf,selectedEventState) where
      (trf@(Trf mgr addprops addlaw _ _), shiftRel) = shiftPrepare bls trfUnshifted
      eventFactsDd = relabelWith mgr (map (bimap fromEnum fromEnum) shiftRel) eventFactsDdUnshifted
      selectedEventsDD = con mgr eventFactsDd (restrictSet mgr (ddOf  bls addlaw) [ (k, P k `elem` s) | P k <- vocabOf bls ])
      eventVoc = map fromEnum addprops
      -- FIXME: avoid the conversion to BDD here - needs allSatsWith for ZDDs
      selectedEvents = allSatsWith mgr eventVoc (toB mgr (toO1 mgr (toI1 mgr eventVoc selectedEventsDD)))
      selectedEventState :: KnState
      selectedEventState =
        case selectedEvents of
          []     -> error "no selected event"
          [this] -> map (P . fst) $ filter snd this
          more   -> error $ "too many selected events: " ++ show more

-- TODO: instance Update (MultipointedBelScene a b c) (MultipointedEvent a b c)

-- TODO: test trfPost with addprops for dependentVars call
trfPost :: (DdCtx a b c) => Event a b c -> Prp -> Dd a b c
trfPost (Trf mgr addprops _ changelaw _, x) p
  | p `elem` M.keys changelaw = restrictLaw mgr (map fromEnum addprops) (changelaw ! p) (boolDDoutof mgr x addprops)
  | otherwise                 = boolDdOf mgr $ PrpF p

reduce :: (DdCtx a b c) => Event a b c -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = Just $ Neg $ preOf e
reduce e@(Trf mgr v _ _ _, _) (PrpF p)     = Impl (preOf e) <$> Just (ddToForm mgr v $ trfPost e p)
reduce e (Neg f)      = Impl (preOf e) <$> (Neg <$> reduce e f)
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (preOf e) <$> (Xor <$> mapM (reduce e) fs)
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce e@(t@(Trf mgr addprops _ _ eventObs), x) (K a f) =
  Impl (preOf e) <$> (Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME: this is inefficient
                             , tagDdEval mgr (mv x ++ cp y) (eventObs ! a)
    ])
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ PubAnnounceW {} = Nothing
reduce _ Announce     {} = Nothing
reduce _ AnnounceW    {} = Nothing
reduce _ Dia          {} = Nothing
