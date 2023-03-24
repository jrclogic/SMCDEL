{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

module SMCDEL.Symbolic.Ki where

import Data.Tagged

import Control.Arrow (first)
import Data.Dynamic (fromDynamic)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (sort,intersect,(\\))
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

import SMCDEL.Internal.Help (apply,lfp,powerset)
import SMCDEL.Language
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.S5 (State,boolBddOf,texBddWith,bddEval,relabelWith)
import SMCDEL.Translations.S5 (booloutof)

mvP, cpP :: Int -> Prp -> Prp
mvP m (P n) = P ((2*n) +m)     -- represent p  in the double vocabulary
cpP m (P n) = P ((2*n) + 1+m) -- represent p' in the double vocabulary

unmvcpP :: Int -> Prp -> Prp
unmvcpP m (P n) | even (n-m)    = P $ (n-m) `div` 2
              | otherwise = P $ (n-m-1) `div` 2

mv, cp :: Int -> [Prp] -> [Prp]
mv m = map $ mvP m
cp m = map $ cpP m

unmv, uncp :: Int -> [Prp] -> [Prp]
-- | Go from p in double vocabulary to p in single vocabulary.
unmv m = map f where
  f (P n) | odd m    = error "unmv failed: Number is odd!"
          | otherwise = P $ (n-m) `div` 2
-- | Go from p' in double vocabulary to p in single vocabulary.
uncp m = map f where
  f (P n) | even m    = error "uncp failed: Number is even!"
          | otherwise = P $ (n-m-1) `div` 2

data Dubbel
type RelBDD = Tagged Dubbel Bdd

totalRelBdd, emptyRelBdd :: RelBDD
totalRelBdd = pure $ boolBddOf Top
emptyRelBdd = pure $ boolBddOf Bot

allsamebdd :: Int -> [Prp] -> RelBDD
allsamebdd m ps = pure $ conSet [boolBddOf $ PrpF p `Equi` PrpF p' | (p,p') <- zip (mv m ps) (cp m ps)]

class TagBdd a where
  tagBddEval :: [Prp] -> Tagged a Bdd -> Bool
  tagBddEval truths querybdd = evaluateFun (untag querybdd) (\n -> P n `elem` truths)

instance TagBdd Dubbel

cpBdd :: Int -> Bdd -> RelBDD
cpBdd m b = Tagged $ relabelFun (\n -> (2*n) + m + 1) b

mvBdd :: Int -> Bdd -> RelBDD
mvBdd m b = Tagged $ relabelFun (\n -> (2 * n) + m) b

unmvBdd :: Int -> RelBDD -> Bdd
unmvBdd m (Tagged b) =
  relabelFun (\n -> if even (n-m) then (n-m) `div` 2 else error ("Not even: " ++ show n)) b

data BelStruct = BlS [Prp]              -- vocabulary
                     Bdd                -- state law
                     (M.Map Agent Int, RelBDD) -- observation laws
                  deriving (Eq,Show)

instance Pointed BelStruct State
type BelScene = (BelStruct,State)

instance Pointed BelStruct Bdd
type MultipointedBelScene = (BelStruct,Bdd)

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ (ag, _)) = M.keys ag

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

bddOf bls@(BlS allprops lawbdd (ags, obdds)) (K i form) = unmvBdd (M.size ags) result where
  result = forallSet ps' <$> (imp <$> cpBdd (M.size ags) lawbdd <*> (imp <$> omegai <*> cpBdd (M.size ags) (bddOf bls form)))
  ps'    = map fromEnum $ cp (M.size ags) allprops
  omegai = Tagged $ restrict (untag obdds) (ags ! i, True)

bddOf bls@(BlS allprops lawbdd (ags, obdds)) (Kw i form) = unmvBdd (M.size ags) result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd (M.size ags) lawbdd <*> (imp <$> omegai <*> cpBdd (M.size ags) (bddOf bls f)))
  ps'    = map fromEnum $ cp (M.size ags) allprops
  omegai = Tagged $ restrict (untag obdds) (ags ! i, True)

bddOf bls@(BlS voc lawbdd (ag,obdds)) (Ck ags form) = lfp lambda top where
  ps' = map fromEnum $ cp (M.size ag) voc
  lambda :: Bdd -> Bdd
  lambda z = unmvBdd (M.size ag) $
    forallSet ps' <$>
      (imp <$> cpBdd (M.size ag) lawbdd <*>
        (imp <$> (disSet <$> sequence [Tagged $ restrict (untag obdds) (ag ! i, True) | i <- ags]) <*>
          cpBdd (M.size ag) (con (bddOf bls form) z))) 

bddOf bls (Ckw ags form) = dis (bddOf bls (Ck ags form)) (bddOf bls (Ck ags (Neg form)))

bddOf bls (PubAnnounce f g) =
  imp (bddOf bls f) (bddOf (bls `update` f) g)
bddOf bls (PubAnnounceW f g) =
  ifthenelse (bddOf bls f)
    (bddOf (bls `update` f    ) g)
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
  isTrue (kns@(BlS _ lawBdd _), statesBdd) f =
    let a = imp lawBdd (imp statesBdd (bddOf kns f))
     in a == top

instance Update BelStruct Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate bls@(BlS allprops lawdd obs) f =
    BlS allprops (con lawdd (bddOf bls f)) obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi,s)

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS props lawbdd (ag,obdds)) ags psi = BlS newprops newlawbdd (ag,newobdds) where
  (P k)     = freshp props
  newprops  = sort $ P k : props
  newlawbdd = con lawbdd (imp (var k) (bddOf bls psi))
  newobdds  = foldl (\x y -> con <$> x <*> y) (Tagged top) [newOfor i $ Tagged (restrict (untag obdds) (ag ! i, True)) | i <- M.keys ag]
  newOfor i oi | i `elem` ags = con <$> oi <*> (equ <$> mvBdd (M.size ag) (var k) <*> cpBdd (M.size ag) (var k))
               | otherwise    = con <$> oi <*> (neg <$> cpBdd (M.size ag) (var k)) -- p_psi'

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

-- TODO: Optimization of Ki structures

-- TODO: Generating Arbitrary Ki structures

data Transformer = Trf
  [Prp] -- addprops
  Form  -- event law
  (M.Map Prp Bdd) -- changelaw
  (M.Map Agent Int, RelBDD) -- eventObs
  deriving (Eq,Show)

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ (ags,_)) = M.keys ags

instance HasPrecondition Transformer where
  preOf _ = Top

instance Pointed Transformer State
type Event = (Transformer,State)

instance HasPrecondition Event where
  preOf (Trf addprops addlaw _ _, x) = simplify $ substitOutOf x addprops addlaw

instance Pointed Transformer [State]
type MultipointedEvent = (Transformer,Bdd)

instance HasPrecondition MultipointedEvent where
  preOf (Trf addprops addlaw _ _, xsBdd) =
    simplify $ Exists addprops (Conj [ formOf xsBdd, addlaw ])

-- TODO: TexAble Transformer

-- | shift addprops to ensure that props and newprops are disjoint:
shiftPrepare :: BelStruct -> Transformer -> (Transformer, [(Prp,Prp)])
shiftPrepare (BlS props _ _) (Trf addprops addlaw changelaw (ags, eventObs)) =
  (Trf shiftaddprops addlawShifted changelawShifted (ags, eventObsShifted), shiftrel) where
    shiftrel = sort $ zip addprops [(freshp props)..]
    shiftaddprops = map snd shiftrel
    -- apply the shifting to addlaw, changelaw and eventObs:
    addlawShifted    = replPsInF shiftrel addlaw
    changelawShifted = M.map (relabelWith shiftrel) changelaw
    -- to shift addObs we need shiftrel in the double vocabulary:
    shiftrelMVCP = sort $ zip (mv (M.size ags) addprops) (mv (M.size ags) shiftaddprops)
                       ++ zip (cp (M.size ags) addprops) (cp (M.size ags) shiftaddprops)
    eventObsShifted  = foldl (\x y -> con <$> x <*> y) (Tagged top) [Tagged $ relabelWith shiftrelMVCP (restrict (untag eventObs) (ags ! i, True)) | i <- M.keys ags]

instance Update BelScene Event where
  unsafeUpdate (bls@(BlS props law (ags, obdds)),s) (trf, eventFactsUnshifted) = (BlS newprops newlaw (ags, newobs), news) where
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    (Trf addprops addlaw changelaw (ag, addObs), shiftrel) = shiftPrepare bls trf
    -- the actual event:
    eventFacts = map (apply shiftrel) eventFactsUnshifted
    -- PART 2: COPYING the modified propositions
    changeprops = M.keys changelaw
    copyrel = zip changeprops [(freshp $ props ++ addprops)..]
    copychangeprops = map snd copyrel
    copyrelMVCP = sort $ zip (mv (M.size ags) changeprops) (mv (M.size ags) copychangeprops)
                      ++ zip (cp (M.size ags) changeprops) (cp (M.size ags) copychangeprops)
    -- PART 3: actual transformation
    newprops = sort $ props ++ addprops ++ copychangeprops
    newlaw = conSet $ relabelWith copyrel (con law (bddOf bls addlaw))
                    : [var (fromEnum q) `equ` relabelWith copyrel (changelaw ! q) | q <- changeprops]
    newobs = foldl (\x y -> con <$> x <*> y) (Tagged top) newobdds
    newobdds = [con <$> (relabelWith copyrelMVCP <$> Tagged (restrict (untag obdds) (ag ! i, True))) <*> Tagged (restrict (untag addObs) (ag ! i, True)) | i <- M.keys ag]
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
reduce e@(t@(Trf addprops _ _ (ags, eventObs)), x) (K a f) =
  Impl (preOf e) <$> (Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME this is inefficient
                             , tagBddEval (mv (M.size ags) x ++ cp (M.size ags) y) (Tagged $ restrict (untag eventObs) (ags ! a, True) :: Tagged Dubbel Bdd)
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
