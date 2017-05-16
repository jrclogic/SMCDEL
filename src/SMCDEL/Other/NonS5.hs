
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TypeOperators #-}

module SMCDEL.Other.NonS5 where

-- import SMCDEL.Other.InVocab
import Data.Tagged

import Control.Arrow ((&&&),(***),first)
import Data.GraphViz
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (nub,intercalate,sort,(\\),delete)
import Data.Map.Strict (Map,fromList,toList,elems,(!),mapMaybeWithKey)
import qualified Data.Map.Strict
import Data.Maybe (fromJust)

import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD (Scenario,KnState,texBDD,boolBddOf,texBddWith)
import SMCDEL.Explicit.Simple (PointedModel,KripkeModel(KrM),State)
import SMCDEL.Translations hiding (voc)
import SMCDEL.Internal.Help (alleq,apply)
import SMCDEL.Internal.TexDisplay

problemPM :: PointedModel
problemPM = ( KrM [0,1,2,3] [ (alice,[[0],[1,2,3]]), (bob,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]), (1,[(P 1,True ),(P 2,False)])
  , (2,[(P 1,False),(P 2,True )]), (3,[(P 1,False),(P 2,False)]) ], 1::State )

problemKNS :: Scenario
problemKNS = kripkeToKns problemPM

mv :: [Prp] -> [Prp]
mv = map (fromJust . (`lookup` [ (P n, P  (2*n)      ) | n <- [0..] ])) -- represent p in the double vocabulary
cp :: [Prp] -> [Prp]
cp = map (fromJust . (`lookup` [ (P n, P ((2*n) + 1) ) | n <- [0..] ])) -- represent p' in the double vocabulary
unmv :: [Prp] -> [Prp]
unmv = map f where -- Go from p in double vocabulary to p in single vocabulary:
  f (P m) | odd m    = error "unmv failed: Number is odd!"
          | otherwise = P $ m `div` 2
uncp :: [Prp] -> [Prp]
uncp = map f where -- Go from p' in double vocabulary to p in single vocabulary:
  f (P m) | even m    = error "uncp failed: Number is even!"
          | otherwise = P $ (m-1) `div` 2

data Dubbel
type RelBDD = Tagged Dubbel Bdd

triviRelBdd :: RelBDD
triviRelBdd = pure $ boolBddOf Top

cpBdd :: Bdd -> RelBDD
cpBdd b = pure $ case maxVarOf b of
  Nothing -> b
  Just m  -> relabel [ (n, (2*n) + 1) | n <- [0..m] ] b

mvBdd :: Bdd -> RelBDD
mvBdd b = pure $ case maxVarOf b of
  Nothing -> b
  Just m  -> relabel [ (n, 2*n) | n <- [0..m] ] b

unmvBdd :: RelBDD -> Bdd
unmvBdd (Tagged b) = case maxVarOf b of
  Nothing -> b
  Just m  -> relabel [ (2 * n, n) | n <- [0..m] ] b

propRel2bdd :: [Prp] -> Map KnState [KnState] -> RelBDD
propRel2bdd props rel = pure $ disSet (elems $ Data.Map.Strict.mapWithKey linkbdd rel) where
  linkbdd here theres =
    con (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there <- theres ] )

samplerel ::  Map KnState [KnState]
samplerel = fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]

newtype GeneralKripkeModel = GKM (Map State (Map Prp Bool, Map Agent [State]))
  deriving (Eq,Ord,Show)

type GeneralPointedModel = (GeneralKripkeModel, State)

distinctVal :: GeneralKripkeModel -> Bool
distinctVal (GKM m) = Data.Map.Strict.size m == length (nub (map fst (elems m)))

worldsOf :: GeneralKripkeModel -> [State]
worldsOf (GKM m) = Data.Map.Strict.keys m

vocOf :: GeneralKripkeModel -> [Prp]
vocOf (GKM m) = Data.Map.Strict.keys $ fst (head (Data.Map.Strict.elems m))

instance HasAgents GeneralKripkeModel where
  agentsOf (GKM m) = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems m))

relOfIn :: Agent -> GeneralKripkeModel -> Map State [State]
relOfIn i (GKM m) = Data.Map.Strict.map (\x -> snd x ! i) m

truthsInAt :: GeneralKripkeModel -> State -> [Prp]
truthsInAt (GKM m) w = Data.Map.Strict.keys (Data.Map.Strict.filter id (fst (m ! w)))

instance KripkeLike GeneralPointedModel where
  directed = const True
  getNodes (m,_) = map (show . fromEnum &&& labelOf) (worldsOf m) where
    labelOf w = "$" ++ tex (truthsInAt m w) ++ "$"
  getEdges (m, _) =
    concat [ [ (a, show $ fromEnum w, show $ fromEnum v) | v <- relOfIn a m ! w ] | w <- worldsOf m, a <- agentsOf m ]
  getActuals (_,w) = [show $ fromEnum w]

instance TexAble GeneralPointedModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

exampleModel :: GeneralKripkeModel
exampleModel = GKM $ fromList
  [ (1, (fromList [(P 0,True ),(P 1,True )], fromList [(alice,[1]), (bob,[1])] ) )
  , (2, (fromList [(P 0,False),(P 1,True )], fromList [(alice,[1]), (bob,[2])] ) ) ]

examplePointedModel :: GeneralPointedModel
examplePointedModel = (exampleModel,1)

eval :: GeneralPointedModel -> Form -> Bool
eval _     Top           = True
eval _     Bot           = False
eval (m,w) (PrpF p)      = p `elem` truthsInAt m w
eval pm    (Neg f)       = not $ eval pm f
eval pm    (Conj fs)     = all (eval pm) fs
eval pm    (Disj fs)     = any (eval pm) fs
eval pm    (Xor  fs)     = odd $ length (filter id $ map (eval pm) fs)
eval pm    (Impl f g)    = not (eval pm f) || eval pm g
eval pm    (Equi f g)    = eval pm f == eval pm g
eval pm    (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm    (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (GKM m,w) (K   i f)     = all (\w' -> eval (GKM m,w') f) (snd (m ! w) ! i)
eval _     (Ck  _ _)     = error "eval: Ck not implemented " -- TODO common belief?
eval (GKM m,w) (Kw  i f)     = alleq (\w' -> eval (GKM m,w') f) (snd (m ! w) ! i)
eval _     (Ckw _ _)     = error "eval: Ck not implemented "
eval (m,w) (PubAnnounce f g) = not (eval (m,w) f) || eval (pubAnnounceNonS5 m f,w) g
eval (m,w) (PubAnnounceW f g) = eval (pubAnnounceNonS5 m aform, w) g where
  aform | eval (m,w) f = f
        | otherwise     = Neg f
eval (m,w) (Announce listeners f g) = not (eval (m,w) f) || eval newm g where
  newm = (m,w) `productUpdate` announceActionNonS5 (agentsOf m) listeners f
eval (m,w) (AnnounceW listeners f g) = not (eval (m,w) f) || eval newm g where
  newm = (m,w) `productUpdate` announceActionNonS5 (agentsOf m) listeners aform
  aform | eval (m,w) f = f
        | otherwise    = Neg f

pubAnnounceNonS5 :: GeneralKripkeModel -> Form -> GeneralKripkeModel
pubAnnounceNonS5 (GKM m) f = GKM newm where
  newm = mapMaybeWithKey isin m
  isin w' (v,rs) | eval (GKM m,w') f = Just (v,Data.Map.Strict.map newr rs)
                 | otherwise     = Nothing
  newr = filter (`elem` Data.Map.Strict.keys newm)

announceActionNonS5 :: [Agent] -> [Agent] -> Form -> GeneralPointedActionModel
announceActionNonS5 everyone listeners f = (GAM am, 1) where
  am = fromList
    [ (1, (f  , fromList $ [(i,[1]) | i <- listeners] ++ [(i,[2]) | i <- everyone \\ listeners]))
    , (2, (Top, fromList   [(i,[2]) | i <- everyone]) ) ]

relBddOfIn :: Agent -> GeneralKripkeModel -> RelBDD
relBddOfIn i (GKM m)
  | not (distinctVal (GKM m)) = error "m does not have distinct valuations."
  | otherwise = pure $ disSet (elems $ Data.Map.Strict.map linkbdd m) where
    linkbdd (mapPropBool,mapAgentReach)  =
      con
        (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there<-theres ] )
      where
        props = Data.Map.Strict.keys mapPropBool
        here = Data.Map.Strict.keys (Data.Map.Strict.filter id mapPropBool)
        theres = map (truthsInAt (GKM m)) (mapAgentReach ! i)

data GenKnowStruct = GenKnS [Prp] Bdd (Map Agent RelBDD) deriving (Eq,Show)

type GenScenario = (GenKnowStruct,[Prp])

instance HasAgents GenKnowStruct where
  agentsOf (GenKnS _ _ obdds) = Data.Map.Strict.keys obdds

instance HasAgents GenScenario where
  agentsOf = agentsOf . fst

bddOf :: GenKnowStruct -> Form -> Bdd
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

bddOf kns@(GenKnS allprops lawbdd obdds) (K i form) = unmvBdd result where
  result = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf kns form)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf kns@(GenKnS allprops lawbdd obdds) (Kw i form) = unmvBdd result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf kns f)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf _ (Ck _ _)  = error "bddOf: Ck not implemented"
bddOf _ (Ckw _ _) = error "bddOf: Ckw not implemented"

bddOf kns (PubAnnounce f g) =
  imp (bddOf kns f) (bddOf (pubAnnounce kns f) g)
bddOf kns (PubAnnounceW f g) =
  ifthenelse (bddOf kns f)
    (bddOf (pubAnnounce kns f      ) g)
    (bddOf (pubAnnounce kns (Neg f)) g)

bddOf kns@(GenKnS props _ _) (Announce ags f g) =
  imp (bddOf kns f) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce kns ags f) g
    (P k) = freshp props

bddOf kns@(GenKnS props _ _) (AnnounceW ags f g) =
  ifthenelse (bddOf kns f) bdd2a bdd2b where
    bdd2a = restrict (bddOf (announce kns ags f) g) (k,True)
    bdd2b = restrict (bddOf (announce kns ags f) g) (k,False)
    (P k) = freshp props

validViaBdd :: GenKnowStruct -> Form -> Bool
validViaBdd kns@(GenKnS _ lawbdd _) f = top == imp lawbdd (bddOf kns f)

evalViaBdd :: GenScenario -> Form -> Bool
evalViaBdd (kns@(GenKnS allprops _ _),s) f = let
    b    = restrictSet (bddOf kns f) list
    list = [ (n, P n `elem` s) | (P n) <- allprops ]
  in
    case (b==top,b==bot) of
      (True,_) -> True
      (_,True) -> False
      _        -> error $ "evalViaBdd failed: Composite BDD leftover!\n"
        ++ "  kns: " ++ show kns ++ "\n"
        ++ "  s: " ++ show s ++ "\n"
        ++ "  form: " ++ show f ++ "\n"
        ++ "  bddOf kns f: " ++ show (bddOf kns f) ++ "\n"
        ++ "  list: " ++ show list ++ "\n"
        ++ "  b: " ++ show b ++ "\n"

pubAnnounce :: GenKnowStruct -> Form -> GenKnowStruct
pubAnnounce kns@(GenKnS allprops lawbdd obs) f =
  GenKnS allprops (con lawbdd (bddOf kns f)) obs

pubAnnounceOnScn :: GenScenario -> Form -> GenScenario
pubAnnounceOnScn (kns,s) psi = if evalViaBdd (kns,s) psi
                                 then (pubAnnounce kns psi,s)
                                 else error "Liar!"

announce :: GenKnowStruct -> [Agent] -> Form -> GenKnowStruct
announce kns@(GenKnS props lawbdd obdds) ags psi = GenKnS newprops newlawbdd newobdds where
  proppsi@(P k) = freshp props
  [P k'] = cp [proppsi]
  newprops  = proppsi:props
  newlawbdd = con lawbdd (imp (var k) (bddOf kns psi))
  newobdds  = Data.Map.Strict.mapWithKey newOfor obdds
  newOfor i oi | i `elem` ags = con <$> oi <*> pure (equ (var k) (var k'))
               | otherwise    = con <$> oi <*> pure (neg (var k')) -- p_psi'

statesOf :: GenKnowStruct -> [KnState]
statesOf (GenKnS allprops lawbdd _) = map (sort.getTrues) prpsats where
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

instance TexAble GenKnowStruct where
  tex (GenKnS props lawbdd obdds) = concat
    [ " \\left( \n"
    , tex props, ", "
    , bddprefix, texBDD lawbdd, bddsuffix
    , ", "
    , intercalate ", " obddstrings
    , " \\right) \n"
    ] where
        obddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (toList obdds)
        bddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble GenScenario where
  tex (kns, state) = concat
    [ " \\left( \n", tex kns, ", ", tex state, " \\right) \n" ]

genKrp2Kns :: GeneralPointedModel -> GenScenario
genKrp2Kns (m, cur) = (GenKnS vocab lawbdd obdds, truthsInAt m cur) where
  vocab  = vocOf m
  lawbdd = disSet [ booloutof (truthsInAt m w) vocab | w <- worldsOf m ]
  obdds  :: Map Agent RelBDD
  obdds  = fromList [ (i, restrictLaw <$> relBddOfIn i m <*> (con <$> mvBdd lawbdd <*> cpBdd lawbdd)) | i <- agents ]
  agents = agentsOf m

exampleGenScn :: GenScenario
exampleGenScn = genKrp2Kns examplePointedModel

exampleGenStruct :: GenKnowStruct
exampleGenState :: KnState
(exampleGenStruct,exampleGenState) = exampleGenScn

allsamebdd :: [Prp] -> RelBDD
allsamebdd ps = pure $ conSet [boolBddOf $ PrpF p `Equi` PrpF p' | (p,p') <- zip (mv ps) (cp ps)]

mudGenScnInit :: Int -> Int -> GenScenario
mudGenScnInit n m = (GenKnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = fromList [(show i, allsamebdd $ delete (P i) vocab) | i <- [1..n]]
  actual = [P 1 .. P m]

myMudGenScnInit :: GenScenario
myMudGenScnInit = mudGenScnInit 3 3

newtype GeneralActionModel = GAM (Map State (Form, Map Agent [State]))
  deriving (Eq,Ord,Show)
type GeneralPointedActionModel = (GeneralActionModel, State)

eventsOf :: GeneralActionModel -> [State]
eventsOf (GAM am) = Data.Map.Strict.keys am

instance HasAgents GeneralActionModel where
  agentsOf (GAM am) = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems am))

relOfInGAM :: Agent -> GeneralActionModel -> Map State [State]
relOfInGAM i (GAM am) = Data.Map.Strict.map (\x -> snd x ! i) am

instance KripkeLike GeneralPointedActionModel where
  directed = const True
  getNodes (GAM am, _) = map (show &&& labelOf) (eventsOf (GAM am)) where
    labelOf a = "$" ++ tex (fst $ am ! a) ++ "$"
  getEdges (GAM am, _) = concat [ [ (a,show w,show v) | v <- relOfInGAM a (GAM am) ! w ] | w <- eventsOf (GAM am), a <- agentsOf (GAM am) ]
  getActuals (_, cur) = [show cur]
  nodeAts _ True  = [shape BoxShape, style solid]
  nodeAts _ False = [shape BoxShape, style dashed]

instance TexAble GeneralPointedActionModel where tex = tex.ViaDot

productUpdate :: GeneralPointedModel -> GeneralPointedActionModel -> GeneralPointedModel
productUpdate (GKM m, oldcur) (GAM am, act)
  | agentsOf (GKM m) /= agentsOf (GAM am)    = error "productUpdate failed: Agents of GKM and GAM are not the same!"
  | not $ eval (GKM m, oldcur) (fst $ am ! act) = error "productUpdate failed: Actual precondition is false!"
  | otherwise = (GKM $ fromList (map annotate statePairs), newcur) where
    statePairs = zip (concat [ [ (s, a) | eval (GKM m, s) (fst $ am ! a) ] | s <- worldsOf (GKM m), a <- eventsOf (GAM am) ]) [0..]
    annotate ((s,a),news) = (news , (fst $ m ! s, fromList (map reachFor (agentsOf (GKM m))))) where
      reachFor i = (i, [ news' | ((s',a'),news') <- statePairs, s' `elem` snd (m !  s) ! i, a' `elem` snd (am ! a) ! i ])
    newcur = fromJust $ lookup (oldcur,act) statePairs

-- Privately tell alice that P 0, while bob thinks nothing happens.
exampleGenActM :: GeneralActionModel
exampleGenActM = GAM $ fromList
  [ (1, (PrpF (P 0), fromList [(alice,[1]), (bob,[2])] ) )
  , (2, (Top       , fromList [(alice,[2]), (bob,[2])] ) ) ]

examplePointedActM :: GeneralPointedActionModel
examplePointedActM = (exampleGenActM,1)

exampleResult :: GeneralPointedModel
exampleResult = productUpdate examplePointedModel examplePointedActM

data BelTransf = BlT [Prp] Form (Map Agent RelBDD) deriving (Eq,Show)
type GenEvent = (BelTransf,KnState)

belTransform :: GenScenario -> GenEvent -> GenScenario
belTransform (kns@(GenKnS props lawbdd obdds),s) (BlT addprops addlaw eventObs, eventFacts) =
  (GenKnS (props ++ map snd shiftrel) newlawbdd newobs, sort $ s ++ shiftedEventFacts) where
    shiftrel = zip addprops [(freshp props)..]
    shiftrelVars = map (fromEnum *** fromEnum) shiftrel
    newobs = fromList [ (i , con <$> (obdds ! i) <*> (relabel shiftrelVars <$> (eventObs ! i))) | i <- Data.Map.Strict.keys obdds ]
    shiftaddlaw = replPsInF shiftrel addlaw
    newlawbdd = con lawbdd (bddOf kns shiftaddlaw)
    shiftedEventFacts = map (apply shiftrel) eventFacts

instance TexAble BelTransf where
  tex (BlT addprops addlaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", "
    , tex addlaw , ", "
    , intercalate ", " eobddstrings
    , " \\right) \n"
    ] where
        eobddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (toList eventObs)
        bddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble GenEvent where
  tex (blt, eventFacts) = concat
    [ " \\left( \n", tex blt, ", ", tex eventFacts, " \\right) \n" ]

exampleStart :: GenScenario
exampleStart = (GenKnS [P 0] law obs, actual) where
  law    = boolBddOf Top
  obs    = fromList [ ("1", mvBdd $ boolBddOf Top), ("2", allsamebdd [P 0]) ]
  actual = [P 0]

exampleEvent :: GenEvent
exampleEvent = (BlT [P 1] addlaw eventObs, [P 1]) where
  addlaw = PrpF (P 1) `Impl` PrpF (P 0)
  eventObs = fromList [ ("1", allsamebdd [P 1]), ("2", cpBdd . boolBddOf $ Neg (PrpF $ P 1)) ]

exampleBlTresult :: GenScenario
exampleBlTresult = belTransform exampleStart exampleEvent
