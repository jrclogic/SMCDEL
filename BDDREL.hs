
module BDDREL where
import Data.HasCacBDD hiding (Top,Bot)
import Data.List (nub,intercalate,sort,(\\))
import Data.Map.Strict (Map,fromList,elems,(!))
import qualified Data.Map.Strict
import Data.Maybe (fromJust)
import DELLANG
import KNSCAC (Scenario,KnState,texBDD)
import KRIPKEDEL
import SYMDEL

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
-- TODO: improve this with:
-- let xs = M.fromList [(1, '1'), (2, '2')] in M.size xs == (M.size . M.fromList . fmap swap $ M.toList xs)

vocOf :: GeneralKripkeModel a -> [Prp]
vocOf m = Data.Map.Strict.keys $ fst (head (Data.Map.Strict.elems m))

agentsOf :: GeneralKripkeModel a -> [Agent]
agentsOf m = Data.Map.Strict.keys $ snd (head (Data.Map.Strict.elems m))

relOfIn :: Agent -> GeneralKripkeModel a -> Map a [a]
relOfIn i = Data.Map.Strict.map (\x -> snd x ! i)

truthsInAt :: Ord a => GeneralKripkeModel a -> a -> [Prp]
truthsInAt m w = Data.Map.Strict.keys (Data.Map.Strict.filter id (fst (m ! w)))

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

data GenKnowStruct = GenKnS [Prp] Bdd (Map Agent RelBDD) deriving (Show)

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

bddOf _ (Kw _ _) = error "bddOf failed: Kw not implemented"

bddOf _ (Ck _ _)  = error "bddOf failed: Ck not implemented"
bddOf _ (Ckw _ _) = error "bddOf failed: Ckw not implemented"

bddOf kns@(GenKnS allprops lawbdd obdds) (PubAnnounce f g) = imp (bddOf kns f) g' where
  g' = bddOf newkns g
  newkns = GenKnS allprops (con lawbdd (bddOf kns f)) obdds
bddOf _ (PubAnnounceW _ _) = error "bddOf failed: PubAnnounceW not implemented"

bddOf _ (Announce{}) = error "bddOf failed: Announce not implemented"
bddOf _ (AnnounceW{}) = error "bddOf failed: AnnounceW not implemented"

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

statesOf :: GenKnowStruct -> [KnState]
statesOf (GenKnS allprops lawbdd _) = map (sort.translate) resultlists where
  resultlists = map (map convToProp) $ allSatsWith (map (\(P n) -> n) allprops) lawbdd :: [[(Prp, Bool)]]
  convToProp (n,bool) = (P n,bool)
  translate l = map fst (filter snd l)

pubAnnounce :: GenKnowStruct -> Form -> GenKnowStruct
pubAnnounce kns@(GenKnS props lawbdd obs) psi = GenKnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)

pubAnnounceOnScn :: GenScenario -> Form -> GenScenario
pubAnnounceOnScn (kns,s) psi = if evalViaBdd (kns,s) psi
                                 then (BDDREL.pubAnnounce kns psi,s)
                                 else error "Liar!"

texGenStructure :: GenScenario -> String -> IO String
texGenStructure (GenKnS props lawbdd obdds, state) filename = do
  let (bddprefix,bddsuffix) = ("\\begin{array}{l} \\scalebox{0.3}{", "} \\end{array} \n")
  lawbddtex <- texBDD lawbdd
  obddstringspure <- mapM  (texBDD . snd) (Data.Map.Strict.toList obdds)
  let obddstringpairs = zip (map fst (Data.Map.Strict.toList obdds)) obddstringspure
  let obddstrings = map ( \(i,os) -> "O_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix ) obddstringpairs
  let fullstring = " \\left( \n"
        ++ texPropSet props ++ ", "
        ++ bddprefix ++ lawbddtex ++ bddsuffix
        ++ ", " ++ intercalate ", " obddstrings
        ++ " \\right) , " ++ texPropSet state
  _ <- writeFile ("tmp/" ++ filename ++ ".tex") fullstring
  return ("Structure was TeX'd to"++filename)

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
