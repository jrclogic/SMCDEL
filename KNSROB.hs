
module KNSROB where
import Data.GraphViz
import Data.List
import Data.Maybe
import System.IO
import System.Process
import qualified Data.ROBDD
import qualified Data.ROBDD.Types (makeDAG)

import HELP (alleq,rtc)
import DELLANG

type Bdd = Data.ROBDD.ROBDD
top,bot :: Bdd
top = Data.ROBDD.makeTrue
bot = Data.ROBDD.makeFalse
var :: Int -> Bdd
var = Data.ROBDD.makeVar
neg :: Bdd -> Bdd
neg = Data.ROBDD.neg
imp,con,dis,equ,xor :: Bdd -> Bdd -> Bdd
imp = Data.ROBDD.impl
con = Data.ROBDD.and
dis = Data.ROBDD.or
equ = Data.ROBDD.biimpl
xor = Data.ROBDD.xor
anySat :: Data.ROBDD.ROBDD -> Maybe [(Int, Bool)]
anySat = Data.ROBDD.anySat
restrict :: Bdd -> (Int,Bool) -> Bdd
restrict bdd (n,value) = Data.ROBDD.restrict bdd n value
restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet = Data.ROBDD.restrictAll

allSatsWith :: [Int] -> Bdd -> [[(Int,Bool)]]
allSatsWith vars bdd = Data.ROBDD.allSat' bdd vars

satCountWith :: [Int] -> Bdd -> Int
satCountWith vars bdd = length $ allSatsWith vars bdd

conSet :: [Bdd] -> Bdd
conSet [] = top
conSet (b:bs) =
  if bot `elem` (b:bs)
    then bot
    else foldl con b bs

disSet :: [Bdd] -> Bdd
disSet [] = bot
disSet (b:bs) =
  if top `elem` (b:bs)
    then top
    else foldl dis b bs

xorSet :: [Bdd] -> Bdd
xorSet [] = bot
xorSet (b:bs) = foldl xor b bs

existsSet,forallSet :: [Int] -> Bdd -> Bdd
existsSet vars b = Data.ROBDD.applyExists (const id) top b vars
forallSet vars b = Data.ROBDD.applyForAll (const id) top b vars

gfp :: (Bdd -> Bdd) -> Bdd
gfp operator = gfpStep operator top (operator top) where
  gfpStep :: (Bdd -> Bdd) -> Bdd -> Bdd -> Bdd
  gfpStep op current next =
    if current == next
      then current
      else gfpStep op next (op next)

genGraph :: Bdd -> String
genGraph bdd = show $ graphToDot params dag where
  dag = Data.ROBDD.Types.makeDAG bdd
  params = nonClusteredParams { fmtNode = \(_,l) -> [toLabel l] , fmtEdge = \(_,_,l) -> [toLabel l] }

booloutof :: [Prp] -> [Prp] -> Bdd
booloutof ps qs = conSet $
  [ var n | (P n) <- ps ] ++
  [ neg $ var n | (P n) <- qs \\ ps ]

booloutofForm :: [Prp] -> [Prp] -> Form
booloutofForm ps qs = Conj $ [ PrpF p | p <- ps ] ++ [ Neg $ PrpF r | r <- qs \\ ps ]

boolBddOf :: Form -> Bdd
boolBddOf Top           = top
boolBddOf Bot           = bot
boolBddOf (PrpF (P n))  = var n
boolBddOf (Neg form)    = neg$ boolBddOf form
boolBddOf (Conj forms)  = conSet $ map boolBddOf forms
boolBddOf (Disj forms)  = disSet  $ map boolBddOf forms
boolBddOf (Impl f g)    = imp (boolBddOf f) (boolBddOf g)
boolBddOf (Equi f g)    = equ (boolBddOf f) (boolBddOf g)
boolBddOf (Forall ps f) = boolBddOf (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
boolBddOf (Exists ps f) = boolBddOf (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
boolBddOf _             = error "boolBddOf failed: Not a boolean formula."

boolEval :: [Prp] -> Form -> Bool
boolEval truths form =  result where
  result = case anySat finalO of
                Just _  -> True
                Nothing -> False
  finalO   = restrictSet (boolBddOf form) (map (\(P n) -> (n, P n `elem` truths)) (propsInForm form))

data KnowStruct = KnS [Prp] Bdd [(Agent,[Prp])] deriving (Eq,Show)
type KnState = [Prp]
type Scenario = (KnowStruct,KnState)

statesOf :: KnowStruct -> [KnState]
statesOf (KnS props lawbdd _) = map (sort.translate) resultlists where
  resultlists = map (map convToProp) $ allSatsWith (map (\(P n) -> n) props) lawbdd :: [[(Prp, Bool)]]
  convToProp (n,bool) = (P n,bool)
  translate l = map fst (filter snd l)

numberOfStates :: KnowStruct -> Int
numberOfStates (KnS ps lawbdd _) = satCountWith (map (\(P n) -> n) ps) lawbdd

restrictState :: KnState -> [Prp] -> KnState
restrictState s props = filter (`elem` props) s

seteq :: Ord a => Eq a => [a] -> [a] -> Bool
seteq as bs = sort as == sort bs

shareknow :: KnowStruct -> [[Prp]] -> [(KnState,KnState)]
shareknow kns sets = filter rel [ (s,t) | s <- statesOf kns, t <- statesOf kns ]
  where
    rel (x,y) = or [ seteq (restrictState x set) (restrictState y set) | set <- sets ]

comknow :: KnowStruct -> [Agent] -> [(KnState,KnState)]
comknow kns@(KnS _ _ obs) ags = rtc $ shareknow kns (map (fromJust . flip lookup obs) ags)

eval :: Scenario -> Form -> Bool
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
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval scn     (Exists ps f) = eval scn (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (kns@(KnS _ _ obs),s) (K i form) = all (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (restrictState s' oi) (restrictState s oi)) (statesOf kns)
  oi = fromJust $ lookup i obs
eval (kns@(KnS _ _ obs),s) (Kw i form) = alleq (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (restrictState s' oi) (restrictState s oi)) (statesOf kns)
  oi = fromJust $ lookup i obs
eval (kns,s) (Ck ags form)  = all (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> (sort s, sort s') `elem` comknow kns ags) (statesOf kns)
eval (kns,s) (Ckw ags form)  = alleq (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> (sort s, sort s') `elem` comknow kns ags) (statesOf kns)
eval (kns,s) (PubAnnounce form1 form2) =
  not (eval (kns, s) form1) || eval (pubAnnounce kns form1, s) form2
eval (kns,s) (PubAnnounceW form1 form2) =
  if eval (kns, s) form1
    then eval (pubAnnounce kns form1, s) form2
    else eval (pubAnnounce kns (Neg form1), s) form2
eval (kns@(KnS props _ _),s) (Announce ags form1 form2) =
  not (eval (kns, s) form1) || eval (announce kns ags form1, freshp props : s) form2
eval (kns,s) (AnnounceW ags form1 form2) =
  if eval (kns, s) form1
    then eval (announce kns ags form1, s) form2
    else eval (announce kns ags (Neg form1), s) form2

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)

pubAnnounceOnScn :: Scenario -> Form -> Scenario
pubAnnounceOnScn (kns,s) psi =
  if eval (kns,s) psi
    then (pubAnnounce kns psi,s)
    else error "Liar!"

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (imp (var k) (bddOf kns psi))
  newobs    = [(i, fromJust (lookup i obs) ++ [proppsi | i `elem` ags]) | i <- map fst obs]

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
    otherps = map (\(P n) -> n) $ allprops \\ fromJust (lookup i obs)
bddOf kns@(KnS allprops lawbdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawbdd (bddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ fromJust (lookup i obs)
bddOf kns@(KnS allprops lawbdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ bddOf kns form : [ forallSet (otherps i) (imp lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ fromJust (lookup i obs)
bddOf kns (Ckw ags form) =
  dis (bddOf kns (Ckw ags form)) (bddOf kns (Ckw ags (Neg form)))
bddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  imp (bddOf kns form1) (restrict bdd2 (k,True)) where
    bdd2  = bddOf (announce kns ags form1) form2
    (P k) = freshp props
bddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  con (imp (bddOf kns form1) bdd2a) (imp (neg $ bddOf kns form1) bdd2b) where
    bdd2a = restrict (bddOf (announce kns ags form1) form2) (k,True)
    bdd2b = restrict (bddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
bddOf kns (PubAnnounce form1 form2) = imp (bddOf kns form1) newform2 where
    newform2 = bddOf (pubAnnounce kns form1) form2
bddOf kns (PubAnnounceW form1 form2) =
  con (imp (bddOf kns form1) newform2a) (imp (neg $ bddOf kns form1) newform2b)  where
    newform2a = bddOf (pubAnnounce kns form1) form2
    newform2b = bddOf (pubAnnounce kns (Neg form1)) form2

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == imp lawbdd (bddOf kns f)

evalViaBdd :: Scenario -> Form -> Bool
evalViaBdd (kns@(KnS allprops _ _),s) f = bool where
  bool
    | b==top = True
    | b==bot = False
    | otherwise = error ("evalViaBdd failed: BDD leftover:\n" ++ show b)
  b    = restrictSet (bddOf kns f) list
  list = [ (n,True) | (P n) <- s ] ++ [ (n,False) | (P n) <- allprops \\ s ]

data KnowTransf = KnT [Prp] Form [(Agent,[Prp])] deriving (Eq,Show)

type Event = (KnowTransf,KnState)

knowTransform :: Scenario -> Event -> Scenario
knowTransform (kns@(KnS props lawbdd obs),s) (KnT addprops addlaw eventobs, eventfacts) =
  (KnS (props ++ map snd shiftrel) newlawbdd newobs, s++shifteventfacts) where
    shiftrel = zip addprops [(freshp props)..]
    newobs = [ (i , sort $ fromJust (lookup i obs) ++ map (fromJust . flip lookup shiftrel) (fromJust $ lookup i eventobs)) | i <- map fst obs ]
    shiftaddlaw = replPsInF shiftrel addlaw
    newlawbdd = con lawbdd (bddOf kns shiftaddlaw)
    shifteventfacts = map (fromJust . flip lookup shiftrel) eventfacts

texBDD :: Bdd -> IO String
texBDD b = do
  putStrLn "Running dot2tex ..."
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  hPutStr i (genGraph b)
  hGetContents o

texStructure :: Scenario -> String -> IO String
texStructure (KnS props lawbdd obs, state) filename = do
  lawbddtex <- texBDD lawbdd
  let fullstring = " \\left( \n"
        ++ texPropSet props ++ ", "
        ++ " \\begin{array}{l} \\scalebox{0.4}{"++lawbddtex++"} \\end{array}\n "
        ++ ", \\begin{array}{l}\n"
        ++ intercalate " \\\\\n " (map (\(_,os) -> (texPropSet os)) obs)
        ++ "\\end{array}\n"
        ++ " \\right) , " ++ texPropSet state
  _ <- writeFile ("tmp/" ++ filename ++ ".tex") fullstring
  return ("Structure was TeX'd to"++filename)
