{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TypeOperators #-}

module SMCDEL.Symbolic.K where

import Data.Tagged

import Control.Arrow ((&&&),(***),first)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (intercalate,sort)
import Data.Map.Strict (Map,fromList,toList,elems,(!))
import qualified Data.Map.Strict

import SMCDEL.Language
import SMCDEL.Symbolic.S5 (KnowScene,State,texBDD,boolBddOf,texBddWith)
import SMCDEL.Explicit.S5 (PointedModelS5,KripkeModelS5(KrMS5),World)
import SMCDEL.Explicit.K
import SMCDEL.Translations.S5
import SMCDEL.Internal.Help (apply,lfp)
import SMCDEL.Internal.TexDisplay

problemPM :: PointedModelS5
problemPM = ( KrMS5 [0,1,2,3] [ (alice,[[0],[1,2,3]]), (bob,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]), (1,[(P 1,True ),(P 2,False)])
  , (2,[(P 1,False),(P 2,True )]), (3,[(P 1,False),(P 2,False)]) ], 1::World )

problemKNS :: KnowScene
problemKNS = kripkeToKns problemPM

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
unmv = map f where -- Go from p in double vocabulary to p in single vocabulary:
  f (P m) | odd m    = error "unmv failed: Number is odd!"
          | otherwise = P $ m `div` 2
uncp = map f where -- Go from p' in double vocabulary to p in single vocabulary:
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

propRel2bdd :: [Prp] -> Map State [State] -> RelBDD
propRel2bdd props rel = pure $ disSet (elems $ Data.Map.Strict.mapWithKey linkbdd rel) where
  linkbdd here theres =
    con (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there <- theres ] )

samplerel ::  Map State [State]
samplerel = fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]

relBddOfIn :: Agent -> KripkeModel -> RelBDD
relBddOfIn i (KrM m)
  | not (distinctVal (KrM m)) = error "m does not have distinct valuations."
  | otherwise = pure $ disSet (elems $ Data.Map.Strict.map linkbdd m) where
    linkbdd (mapPropBool,mapAgentReach)  =
      con
        (booloutof (mv here) (mv props))
        (disSet [ booloutof (cp there) (cp props) | there<-theres ] )
      where
        props = Data.Map.Strict.keys mapPropBool
        here = Data.Map.Strict.keys (Data.Map.Strict.filter id mapPropBool)
        theres = map (truthsInAt (KrM m)) (mapAgentReach ! i)

data BelStruct = BlS [Prp]              -- vocabulary
                     Bdd                -- state law
                     (Map Agent RelBDD) -- observation laws
                  deriving (Eq,Show)

type BelScene = (BelStruct,State)

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasVocab BelScene where
  vocabOf = vocabOf . fst

instance HasAgents BelStruct where
  agentsOf (BlS _ _ obdds) = Data.Map.Strict.keys obdds

instance HasAgents BelScene where
  agentsOf = agentsOf . fst

bddOf :: BelStruct -> Form -> Bdd
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

bddOf kns@(BlS allprops lawbdd obdds) (K i form) = unmvBdd result where
  result = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf kns form)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf kns@(BlS allprops lawbdd obdds) (Kw i form) = unmvBdd result where
  result = dis <$> part form <*> part (Neg form)
  part f = forallSet ps' <$> (imp <$> cpBdd lawbdd <*> (imp <$> omegai <*> cpBdd (bddOf kns f)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf kns@(BlS voc lawbdd obdds) (Ck ags form) = lfp lambda top where
  ps' = map fromEnum $ cp voc
  lambda :: Bdd -> Bdd
  lambda z = unmvBdd $
    forallSet ps' <$>
      (imp <$> cpBdd lawbdd <*>
        (imp <$> (disSet <$> sequence [obdds ! i | i <- ags]) <*>
          cpBdd (con (bddOf kns form) z)))

bddOf kns (Ckw ags form) = dis (bddOf kns (Ck ags form)) (bddOf kns (Ck ags (Neg form)))

bddOf kns (PubAnnounce f g) =
  imp (bddOf kns f) (bddOf (pubAnnounce kns f) g)
bddOf kns (PubAnnounceW f g) =
  ifthenelse (bddOf kns f)
    (bddOf (pubAnnounce kns f      ) g)
    (bddOf (pubAnnounce kns (Neg f)) g)

bddOf kns@(BlS props _ _) (Announce ags f g) =
  imp (bddOf kns f) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce kns ags f) g
    (P k) = freshp props

bddOf kns@(BlS props _ _) (AnnounceW ags f g) =
  ifthenelse (bddOf kns f) bdd2a bdd2b where
    bdd2a = restrict (bddOf (announce kns ags f      ) g) (k,True)
    bdd2b = restrict (bddOf (announce kns ags (Neg f)) g) (k,True)
    (P k) = freshp props

validViaBdd :: BelStruct -> Form -> Bool
validViaBdd kns@(BlS _ lawbdd _) f = top == imp lawbdd (bddOf kns f)

evalViaBdd :: BelScene -> Form -> Bool
evalViaBdd (kns@(BlS allprops _ _),s) f = let
    bdd  = bddOf kns f
    b    = restrictSet bdd list
    list = [ (n, P n `elem` s) | (P n) <- allprops ]
  in
    case (b==top,b==bot) of
      (True,_) -> True
      (_,True) -> False
      _        -> error $ "evalViaBdd failed: Composite BDD leftover!\n"
        ++ "  kns:  " ++ show kns ++ "\n"
        ++ "  s:    " ++ show s ++ "\n"
        ++ "  form: " ++ show f ++ "\n"
        ++ "  bdd:  " ++ show bdd ++ "\n"
        ++ "  list: " ++ show list ++ "\n"
        ++ "  b:    " ++ show b ++ "\n"

pubAnnounce :: BelStruct -> Form -> BelStruct
pubAnnounce kns@(BlS allprops lawbdd obs) f =
  BlS allprops (con lawbdd (bddOf kns f)) obs

pubAnnounceOnScn :: BelScene -> Form -> BelScene
pubAnnounceOnScn (kns,s) psi = if evalViaBdd (kns,s) psi
                                 then (pubAnnounce kns psi,s)
                                 else error "Liar!"

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce kns@(BlS props lawbdd obdds) ags psi = BlS newprops newlawbdd newobdds where
  (P k)     = freshp props
  newprops  = sort $ P k : props
  newlawbdd = con lawbdd (imp (var k) (bddOf kns psi))
  newobdds  = Data.Map.Strict.mapWithKey newOfor obdds
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
        obddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (toList obdds)
        bddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble BelScene where
  tex (kns, state) = concat
    [ " \\left( \n", tex kns, ", ", tex state, " \\right) \n" ]

cleanupObsLaw :: BelScene -> BelScene
cleanupObsLaw (BlS vocab law obs, s) = (BlS vocab law newobs, s) where
  newobs = Data.Map.Strict.map optimize obs
  optimize relbdd = restrictLaw <$> relbdd <*> (con <$> cpBdd law <*> mvBdd law)

determinedVocabOf :: BelStruct -> [Prp]
determinedVocabOf strct = filter (\p -> validViaBdd strct (PrpF p) || validViaBdd strct (Neg $ PrpF p)) (vocabOf strct)

nonobsVocabOf  :: BelStruct -> [Prp]
nonobsVocabOf (BlS vocab _law obs) = filter (`notElem` usedVars) vocab where
  usedVars =
    map unmvcpP
    $ sort
    $ concatMap (map P . Data.HasCacBDD.allVarsOf . untag . snd)
    $ Data.Map.Strict.toList obs

data BelTransf = BlT [Prp] Form (Map Agent RelBDD) deriving (Eq,Show)
type GenEvent = (BelTransf,State)

belTransform :: BelScene -> GenEvent -> BelScene
belTransform (kns@(BlS props lawbdd obdds),s) (BlT addprops addlaw eventObs, eventFacts) =
  (BlS (props ++ map snd shiftrel) newlawbdd newobs, sort $ s ++ shiftedEventFacts) where
    shiftrel = zip addprops [(freshp props)..]
    doubleShiftrel = map (mvP *** mvP) shiftrel ++ map (cpP *** cpP) shiftrel
    doubleShiftrelVars = sort $ map (fromEnum *** fromEnum) doubleShiftrel
    shiftEventObsBDD o = relabel doubleShiftrelVars <$> o
    newobs = fromList [ (i , con <$> (obdds ! i) <*> shiftEventObsBDD (eventObs ! i)) | i <- Data.Map.Strict.keys obdds ]
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

exampleStart :: BelScene
exampleStart = (BlS [P 0] law obs, actual) where
  law    = boolBddOf Top
  obs    = fromList [ ("1", mvBdd $ boolBddOf Top), ("2", allsamebdd [P 0]) ]
  actual = [P 0]

exampleEvent :: GenEvent
exampleEvent = (BlT [P 1] addlaw eventObs, [P 1]) where
  addlaw = PrpF (P 1) `Impl` PrpF (P 0)
  eventObs = fromList [ ("1", allsamebdd [P 1]), ("2", cpBdd . boolBddOf $ Neg (PrpF $ P 1)) ]

exampleBlTresult :: BelScene
exampleBlTresult = belTransform exampleStart exampleEvent
