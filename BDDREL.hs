
module BDDREL where
import Control.Arrow
import Data.HasCacBDD hiding (Top,Bot)
import Data.List
import Data.Maybe (fromJust)
import DELLANG
import KNSCAC (Scenario,KnState,texBDD)
import KRIPKEDEL
import KRIPKEVIS
import SYMDEL

problemPM :: PointedModel
problemPM = ( KrM [0,1,2,3]
  [ (0,[[0],[1,2,3]]), (1,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]),
    (1,[(P 1,True ),(P 2,False)]),
    (2,[(P 1,False),(P 2,True )]),
    (3,[(P 1,False),(P 2,False)]) ], 1::State )

problemKNS :: Scenario
problemKNS = kripkeToKns problemPM

type RelBDD = Bdd

booloutof :: [Prp] -> [Prp] -> Bdd
booloutof ps qs = conSet $
  [ var n | (P n) <- ps ] ++
  [ neg $ var n | (P n) <- qs \\ ps ]

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

unmvBdd :: Bdd -> Bdd
unmvBdd b | b == bot  = b
	  | b == top  = b
	  | otherwise = relabel [ (2 * n, n) | n <- [0..m] ] b where (Just m) = maxVarOf b

propRel2bdd :: [Prp] -> Rel KnState -> RelBDD 
propRel2bdd voc rel = disSet (map linkbdd rel) where
  linkbdd (here,there) = con (booloutof (mv here) (mv voc)) (booloutof (cp there) (cp voc))

samplerel :: Rel KnState
samplerel = [
  ([],[]), ([],[P 1]), ([],[P 2]), ([],[P 1, P 2]),
  ([P 1],[P 1]), ([P 1],[P 1, P 2]),
  ([P 2],[P 2]), ([P 2],[P 1, P 2]),
  ([P 1, P 2],[P 1, P 2])
  ]

data GeneralKripkeModel = GenKrM [State] [(Agent,Rel State)] [(State,KRIPKEDEL.Assignment)] deriving (Show)

type GeneralPointedModel = (GeneralKripkeModel,State)

myDispModel :: GeneralPointedModel -> IO ()
myDispModel (GenKrM states rel val, cur)
  = dispGenModel show showAgent showVal "" (GenVisModel states rel val cur)

myTexModel :: GeneralPointedModel -> String -> IO String
myTexModel (GenKrM states rel val, cur)
  = texGenModel show showAgent showVal "" (GenVisModel states rel val cur)

exampleModel :: GeneralKripkeModel
exampleModel = GenKrM
  [1,2]
  [ (0,[ (1,2),(2,2) ]),
    (1,[ (1,1),(2,2)       ]) ]
  [ (1,[(P 0,True) ]),
    (2,[(P 0,False)])]

examplePointedModel :: GeneralPointedModel
examplePointedModel = (exampleModel,1::State)

getPropRel :: GeneralKripkeModel -> Agent -> Rel KnState
getPropRel (GenKrM states rel val) i =
  if length (nub (map snd val)) /= length states
    then error "Model does not have distinct valuations."
    else map (translate *** translate) (fromJust $ lookup i rel) where
      translate n = map fst (filter snd $ fromJust $ lookup n val)

relBddFor :: GeneralKripkeModel -> Agent -> RelBDD
relBddFor model@(GenKrM _ _ val) i = propRel2bdd voc (getPropRel model i) where
  voc = (map fst . snd . head) val

data GenKnowStruct = GenKnS [Prp] Bdd [(Agent,RelBDD)] deriving (Eq,Show)

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
  (Just omegai) = lookup i obdds

bddOf _ (Kw _ _) = error "bddOf failed: Kw not implemented"

bddOf _ (Ck _ _)  = error "bddOf failed: Ck not implemented"
bddOf _ (Ckw _ _) = error "bddOf failed: Ckw not implemented"

bddOf kns@(GenKnS allprops lawbdd obdds) (PubAnnounce f g) = imp (bddOf kns f) g' where
  g' = bddOf newkns g
  newkns = GenKnS allprops (con lawbdd (bddOf kns f)) obdds
bddOf _ (PubAnnounceW _ _) = error "bddOf failed: PubAnnounceW not implemented"

bddOf _ (AnnounceW{}) = error "bddOf failed: AnnounceW not implemented"
bddOf kns@(GenKnS allprops lawbdd obdds) (Announce ags f g) = imp (bddOf kns f) g' where
  (P k)     = freshp allprops
  newprops  = sort (P k:allprops)
  newlawbdd = con lawbdd (imp (var k) (bddOf kns f))
  newobdds  = map changeobdd obdds
  changeobdd (i,oi) = if i `elem` ags
    then (i,con oi (equ (var k) (var ((2*k)+1))))
    else (i,oi)
  newkns = GenKnS newprops newlawbdd newobdds
  g'     = restrict (bddOf newkns g) (k,True)

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

texGenStructure :: GenScenario -> String -> IO String
texGenStructure (GenKnS props lawbdd obdds, state) filename = do
  let (bddprefix,bddsuffix) = ("\\begin{array}{l} \\scalebox{0.4}{", "} \\end{array} \n")
  lawbddtex <- texBDD lawbdd
  obddstringspure <- mapM  (texBDD . snd) obdds
  let obddstringpairs = zip (map fst obdds) obddstringspure
  let obddstrings = map ( \(i,os) -> "O_" ++ show i ++ " = " ++ bddprefix ++ os ++ bddsuffix ) obddstringpairs
  let fullstring = " \\left( \n"
	++ texPropSet props ++ ", "
	++ bddprefix ++ lawbddtex ++ bddsuffix
	++ ", " ++ intercalate ", " obddstrings
	++ " \\right) , " ++ texPropSet state
  _ <- writeFile ("tmp/" ++ filename ++ ".tex") fullstring
  return ("Structure was TeX'd to"++filename)

genKrp2Kns :: GeneralPointedModel -> GenScenario
genKrp2Kns (pm@(GenKrM states rel val), cur) = (GenKnS voc lawbdd obdds, trAt cur) where
  voc    = (map fst . snd . head) val
  lawbdd = disSet [ booloutof (trAt s) voc | s <- states ]
  obdds  = [ (i, relBddFor pm i ) | i <- agents ]
  agents = map fst rel
  trAt s = map fst $ filter snd (fromJust $ lookup s val)
  
exampleGenScn :: GenScenario
exampleGenScn = genKrp2Kns examplePointedModel

exampleGenStruct :: GenKnowStruct
exampleGenState :: KnState
(exampleGenStruct,exampleGenState) = exampleGenScn
