
module KNSCUDD where
import MyCUDD
import Data.List (sort,intercalate,(\\))
import System.IO (hPutStr, hGetContents)
import System.Process (runInteractiveCommand)
import HELP (alleq,apply,rtc)
import DELLANG

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
boolEval truths form = result where
  values = map (\(P n) -> (n, P n `elem` truths)) (propsInForm form)
  bdd    = restrictSet (boolBddOf form) values
  result | bdd==top  = True
         | bdd==bot  = False
         | otherwise = error "boolEval failed: BDD leftover."

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
shareknow kns sets = filter rel [ (s,t) | s <- statesOf kns, t <- statesOf kns ] where
  rel (x,y) = or [ seteq (restrictState x set) (restrictState y set) | set <- sets ]

comknow :: KnowStruct -> [Agent] -> [(KnState,KnState)]
comknow kns@(KnS _ _ obs) ags = rtc $ shareknow kns (map (apply obs) ags)

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
  oi = apply obs i
eval (kns@(KnS _ _ obs),s) (Kw i form) = alleq (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (restrictState s' oi) (restrictState s oi)) (statesOf kns)
  oi = apply obs i
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
pubAnnounceOnScn (kns,s) psi = if eval (kns,s) psi
                                 then (pubAnnounce kns psi,s)
                                 else error "Liar!"

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (imp (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

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
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
bddOf kns@(KnS allprops lawbdd obs) (Kw i form) =
  disSet [ forallSet otherps (imp lawbdd (bddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
bddOf kns@(KnS allprops lawbdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ bddOf kns form : [ forallSet (otherps i) (imp lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
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
bddOf kns (PubAnnounce form1 form2) = imp (bddOf kns form1) newform2 where
    newform2 = bddOf (pubAnnounce kns form1) form2
bddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (bddOf kns form1) newform2a newform2b where
    newform2a = bddOf (pubAnnounce kns form1) form2
    newform2b = bddOf (pubAnnounce kns (Neg form1)) form2

evalViaBdd :: Scenario -> Form -> Bool
evalViaBdd (kns@(KnS allprops _ _),s) f = bool where
  bool | b==top = True
       | b==bot = False
       | otherwise = error ("evalViaBdd failed: BDD leftover:\n" ++ show b)
  b    = restrictSet (bddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f

data KnowTransf = KnT [Prp] Form [(Agent,[Prp])] deriving (Eq,Show)
type Event = (KnowTransf,KnState)

knowTransform :: Scenario -> Event -> Scenario
knowTransform (kns@(KnS props lawbdd obs),s) (KnT addprops addlaw eventobs, eventfacts) =
  (KnS (props ++ map snd shiftrel) newlawbdd newobs, s++shifteventfacts) where
    shiftrel = zip addprops [(freshp props)..]
    newobs = [ (i , sort $ apply obs i ++ map (apply shiftrel) (apply eventobs i)) | i <- map fst obs ]
    shiftaddlaw = replPsInF shiftrel addlaw
    newlawbdd = con lawbdd (bddOf kns shiftaddlaw)
    shifteventfacts = map (apply shiftrel) eventfacts

texBDD :: Bdd -> IO String
texBDD b = do
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
