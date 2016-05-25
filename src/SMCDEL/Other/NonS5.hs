
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module SMCDEL.Other.NonS5 where
import Control.Arrow ((&&&))
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (nub,intercalate,sort,(\\),delete)
import Data.Map.Strict (Map,fromList,elems,(!),mapMaybeWithKey,mapKeys,union)
import qualified Data.Map.Strict
import Data.Maybe (fromJust)
import SMCDEL.Language
import SMCDEL.Symbolic.HasCacBDD (Scenario,KnState,texBDD,boolBddOf)
import SMCDEL.Explicit.Simple (PointedModel,KripkeModel(KrM),State)
import SMCDEL.Translations hiding (voc)
import SMCDEL.Internal.Help (alleq)
import SMCDEL.Internal.TexDisplay

problemPM :: PointedModel
problemPM = ( KrM [0,1,2,3] [ (alice,[[0],[1,2,3]]), (bob,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]), (1,[(P 1,True ),(P 2,False)])
  , (2,[(P 1,False),(P 2,True )]), (3,[(P 1,False),(P 2,False)]) ], 1::State )

problemKNS :: Scenario
problemKNS = kripkeToKns problemPM

type RelBDD = Bdd

mv :: [Prp] -> [Prp]
mv = map (fromJust . (`lookup` [ (P n, P  (2*n)      ) | n <- [0..] ])) -- represent p in the double vocabulary
cp :: [Prp] -> [Prp]
cp = map (fromJust . (`lookup` [ (P n, P ((2*n) + 1) ) | n <- [0..] ])) -- represent p' in the double vocabulary
unprime :: [Prp] -> [Prp]
-- Go from p' in double vocabulary to p in single vocabulary:
unprime = map f where
  f (P m) | even m = error "unprime failed: Number is even!"
          | otherwise = P $ fromJust (lookup m [ ((2*n) + 1, n) | n <- [0..] ])

cpBdd :: Bdd -> Bdd
cpBdd b | b == bot  = b
        | b == top  = b
        | otherwise = relabel [ (n, (2*n) + 1) | n <- [0..m] ] b where (Just m) = maxVarOf b

mvBdd :: Bdd -> Bdd
mvBdd b | b == bot  = b
        | b == top  = b
        | otherwise = relabel [ (n, 2*n) | n <- [0..(fromJust $ maxVarOf b)] ] b

unmvBdd :: Bdd -> Bdd
unmvBdd b | b == bot  = b
          | b == top  = b
          | otherwise = relabel [ (2 * n, n) | n <- [0..(fromJust $ maxVarOf b)] ] b

propRel2bdd :: [Prp] -> Map KnState [KnState] -> RelBDD
propRel2bdd voc rel = disSet (elems $ Data.Map.Strict.mapWithKey linkbdd rel) where
  linkbdd here theres =
    con (booloutof (mv here) (mv voc))
        (disSet [ booloutof (cp there) (cp voc) | there<-theres ] )

samplerel ::  Map KnState [KnState]
samplerel = fromList [
  ( []        , [ [],[P 1],[P 2],[P 1, P 2] ] ),
  ( [P 1]     , [    [P 1],      [P 1, P 2] ] ),
  ( [P 2]     , [    [P 2],      [P 1, P 2] ] ),
  ( [P 1, P 2], [                [P 1, P 2] ] )  ]

type GeneralKripkeModel a = Map a (Map Prp Bool, Map Agent [a])

type GeneralPointedModel a = (GeneralKripkeModel a, a)

exampleModel :: GeneralKripkeModel Int
exampleModel = fromList
  [ (1, (fromList [(P 0,True ),(P 1,True )], fromList [(alice,[1]), (bob,[1])] ) )
  , (2, (fromList [(P 0,False),(P 1,True )], fromList [(alice,[1]), (bob,[2])] ) ) ]

examplePointedModel :: GeneralPointedModel Int
examplePointedModel = (exampleModel,1)

distinctVal :: GeneralKripkeModel a -> Bool
distinctVal m = Data.Map.Strict.size m == length (nub (map fst (elems m)))

vocOf :: GeneralKripkeModel a -> [Prp]
vocOf m = Data.Map.Strict.keys $ fst (head (Data.Map.Strict.elems m))

agentsOf :: GeneralKripkeModel a -> [Agent]
agentsOf m = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems m))

relOfIn :: Agent -> GeneralKripkeModel a -> Map a [a]
relOfIn i = Data.Map.Strict.map (\x -> snd x ! i)

truthsInAt :: Ord a => GeneralKripkeModel a -> a -> [Prp]
truthsInAt m w = Data.Map.Strict.keys (Data.Map.Strict.filter id (fst (m ! w)))

eval :: Ord a => GeneralPointedModel a -> Form -> Bool
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
eval (m,w) (K   i f)     = all (\w' -> eval (m,w') f) (snd (m ! w) ! i)
eval _     (Ck  _ _)     = error "eval: Ck not implemented "
eval (m,w) (Kw  i f)     = alleq (\w' -> eval (m,w') f) (snd (m ! w) ! i)
eval _     (Ckw _ _)     = error "eval: Ck not implemented "
eval (m,w) (PubAnnounce f g) = not (eval (m,w) f) || eval (pubAnnounceNonS5 m f,w) g
eval (m,w) (PubAnnounceW f g) = eval (pubAnnounceNonS5 m aform, w) g where
  aform | eval (m,w) f = f
        | otherwise     = Neg f
eval (m,w) (Announce is f g) =
  not (eval (m,w) f) || eval (announceNonS5 m is f, (w,True)) g
eval (m,w) (AnnounceW is f g) = eval (announceNonS5 m is aform, (w,True)) g where
  aform | eval (m,w) f = f
        | otherwise    = Neg f

pubAnnounceNonS5 :: Ord a => GeneralKripkeModel a -> Form -> GeneralKripkeModel a
pubAnnounceNonS5 m f = newm where
  newm = mapMaybeWithKey isin m
  isin w' (v,rs) | eval (m,w') f = Just (v,Data.Map.Strict.map newr rs)
                 | otherwise     = Nothing
  newr = filter (`elem` Data.Map.Strict.keys newm)

announceNonS5 :: Ord a => GeneralKripkeModel a -> [Agent] -> Form -> GeneralKripkeModel (a,Bool)
announceNonS5 m is f = oldm `union` addm where
  oldm        = mapKeys (\k -> (k,False)) $ Data.Map.Strict.map fixr m
  fixr (v,rs) = (v, Data.Map.Strict.map (map (\k -> (k,False))) rs)
  addm        = mapKeys (\k -> (k,True)) $ mapMaybeWithKey copy m
  copy w' (v,rs) | eval (m,w') f = Just (v,Data.Map.Strict.mapWithKey copyr rs)
                 | otherwise     = Nothing
  copyr i rs | i `elem` is = map (\k -> (k,True)) rs
             | otherwise   = map (\k -> (k,False)) rs

relBddOfIn :: Ord a =>  Agent -> GeneralKripkeModel a -> RelBDD
relBddOfIn i m
  | not (distinctVal m) =  error "m does not have distinct valuations."
  | otherwise = disSet (elems $ Data.Map.Strict.map linkbdd m) where
    linkbdd (mapPropBool,mapAgentReach)  =
      con
        (booloutof (mv here) (mv voc))
        (disSet [ booloutof (cp there) (cp voc) | there<-theres ] )
      where
        voc = Data.Map.Strict.keys mapPropBool
        here = Data.Map.Strict.keys (Data.Map.Strict.filter id mapPropBool)
        theres = map (truthsInAt m) (mapAgentReach ! i)

data GenKnowStruct = GenKnS [Prp] Bdd (Map Agent RelBDD) deriving (Eq,Show)

type GenScenario = (GenKnowStruct,[Prp])

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
  result = forallSet ps' (cpBdd lawbdd `imp` (omegai `imp` cpBdd (bddOf kns form)))
  ps'    = map fromEnum $ cp allprops
  omegai = obdds ! i

bddOf kns@(GenKnS allprops lawbdd obdds) (Kw i form) = unmvBdd result where
  result = disSet (map part [form, Neg form])
  part f = forallSet ps' (cpBdd lawbdd `imp` (omegai `imp` cpBdd (bddOf kns f)))
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
    list = [ (n,True) | (P n) <- s ] ++ [ (n,False) | (P n) <- allprops \\ s ]
  in
    case (b==top,b==bot) of
      (True,_) -> True
      (_,True) -> False
      _        -> error "evalViaBdd failed: Composite BDD leftover."

pubAnnounce :: GenKnowStruct -> Form -> GenKnowStruct
pubAnnounce kns@(GenKnS allprops lawbdd obs) f =
  GenKnS allprops (con lawbdd (bddOf kns f)) obs

pubAnnounceOnScn :: GenScenario -> Form -> GenScenario
pubAnnounceOnScn (kns,s) psi = if evalViaBdd (kns,s) psi
                                 then (SMCDEL.Other.NonS5.pubAnnounce kns psi,s)
                                 else error "Liar!"

announce :: GenKnowStruct -> [Agent] -> Form -> GenKnowStruct
announce kns@(GenKnS props lawbdd obdds) ags psi = GenKnS newprops newlawbdd newobdds where
  proppsi@(P k) = freshp props
  [P k'] = cp [proppsi]
  newprops  = proppsi:props
  newlawbdd = con lawbdd (imp (var k) (bddOf kns psi))
  newobdds  = Data.Map.Strict.mapWithKey newOfor obdds
  newOfor i oi | i `elem` ags = con oi (equ (var k) (var k'))
               | otherwise    = con oi (neg (var k')) -- p_psi'

statesOf :: GenKnowStruct -> [KnState]
statesOf (GenKnS allprops lawbdd _) = map (sort.translate) resultlists where
  resultlists = map (map convToProp) $ allSatsWith (map (\(P n) -> n) allprops) lawbdd :: [[(Prp, Bool)]] -- FIXME ugly
  convToProp (n,bool) = (P n,bool)
  translate l = map fst (filter snd l)

instance TexAble GenScenario where
  tex (GenKnS props lawbdd obdds, state) = concat
    [ " \\left( \n"
    , tex props, ", "
    , bddprefix, texBDD lawbdd, bddsuffix
    , ", "
    , intercalate ", " obddstrings
    , " \\right) , "
    , tex state
    ] where
        (bddprefix,bddsuffix) = ("\\begin{array}{l} \\scalebox{0.3}{", "} \\end{array} \n")
        obddstrings =
          map ( (\(i,os) -> "O_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix).(fst &&& (texBDD . snd)) ) (Data.Map.Strict.toList obdds)

genKrp2Kns :: Ord a => GeneralPointedModel a -> GenScenario
genKrp2Kns (m, cur) = (GenKnS voc lawbdd obdds, truthsInAt m cur) where
  voc    = vocOf m
  lawbdd = disSet [ booloutof (truthsInAt m w) voc | w <- Data.Map.Strict.keys m ]
  obdds  = fromList [ (i, restrictLaw (relBddOfIn i m) (con (mvBdd lawbdd) (cpBdd lawbdd))) | i <- agents ]
  agents = agentsOf m

exampleGenScn :: GenScenario
exampleGenScn = genKrp2Kns examplePointedModel

exampleGenStruct :: GenKnowStruct
exampleGenState :: KnState
(exampleGenStruct,exampleGenState) = exampleGenScn

allsamebdd :: [Prp] -> RelBDD
allsamebdd ps = conSet [boolBddOf $ PrpF p `Equi` PrpF p' | (p,p') <- zip (mv ps) (cp ps)]

mudGenScnInit :: Int -> Int -> GenScenario
mudGenScnInit n m = (GenKnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = fromList [(show i, allsamebdd $ delete (P i) vocab) | i <- [1..n]]
  actual = [P 1 .. P m]

myMudGenScnInit :: GenScenario
myMudGenScnInit = mudGenScnInit 3 3
