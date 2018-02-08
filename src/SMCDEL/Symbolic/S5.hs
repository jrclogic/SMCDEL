
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Symbolic.S5 where
import Control.Arrow (first)
import Data.HasCacBDD hiding (Top,Bot)
import Data.HasCacBDD.Visuals
import Data.List (sort,intercalate,(\\))
import System.IO (hPutStr, hGetContents, hClose)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (runInteractiveCommand)
import SMCDEL.Internal.Help (alleqWith,apply,(!),rtc,seteq,powerset)
import SMCDEL.Language
import SMCDEL.Internal.TexDisplay

boolBddOf :: Form -> Bdd
boolBddOf Top           = top
boolBddOf Bot           = bot
boolBddOf (PrpF (P n))  = var n
boolBddOf (Neg form)    = neg$ boolBddOf form
boolBddOf (Conj forms)  = conSet $ map boolBddOf forms
boolBddOf (Disj forms)  = disSet $ map boolBddOf forms
boolBddOf (Xor forms)   = xorSet $ map boolBddOf forms
boolBddOf (Impl f g)    = imp (boolBddOf f) (boolBddOf g)
boolBddOf (Equi f g)    = equ (boolBddOf f) (boolBddOf g)
boolBddOf (Forall ps f) = forallSet (map fromEnum ps) (boolBddOf f)
boolBddOf (Exists ps f) = existsSet (map fromEnum ps) (boolBddOf f)
boolBddOf _             = error "boolBddOf failed: Not a boolean formula."

boolEvalViaBdd :: [Prp] -> Form -> Bool
boolEvalViaBdd truths = bddEval truths . boolBddOf

bddEval :: [Prp] -> Bdd -> Bool
bddEval truths querybdd = evaluateFun querybdd (\n -> P n `elem` truths)

data KnowStruct = KnS [Prp]            -- vocabulary
                      Bdd              -- state law
                      [(Agent,[Prp])]  -- observational variables
                    deriving (Eq,Show)

type State = [Prp]

type KnowScene = (KnowStruct,State)

statesOf :: KnowStruct -> [State]
statesOf (KnS props lawbdd _) = map (sort.translate) resultlists where
  resultlists :: [[(Prp, Bool)]]
  resultlists = map (map (first toEnum)) $ allSatsWith (map fromEnum props) lawbdd
  translate l = map fst (filter snd l)

instance HasAgents KnowStruct where
  agentsOf (KnS _ _ obs)= map fst obs

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

instance HasAgents KnowScene where agentsOf = agentsOf . fst
instance HasVocab  KnowScene where vocabOf  = vocabOf  . fst

numberOfStates :: KnowStruct -> Int
numberOfStates (KnS props lawbdd _) = satCountWith (map fromEnum props) lawbdd

restrictState :: State -> [Prp] -> State
restrictState s props = filter (`elem` props) s

shareknow :: KnowStruct -> [[Prp]] -> [(State,State)]
shareknow kns sets = filter rel [ (s,t) | s <- statesOf kns, t <- statesOf kns ] where
  rel (x,y) = or [ seteq (restrictState x set) (restrictState y set) | set <- sets ]

comknow :: KnowStruct -> [Agent] -> [(State,State)]
comknow kns@(KnS _ _ obs) ags = rtc $ shareknow kns (map (apply obs) ags)

eval :: KnowScene -> Form -> Bool
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
eval (kns@(KnS _ _ obs),s) (Kw i form) = alleqWith (\s' -> eval (kns,s') form) theres where
  theres = filter (\s' -> seteq (restrictState s' oi) (restrictState s oi)) (statesOf kns)
  oi = apply obs i
eval (kns,s) (Ck ags form)  = all (\s' -> eval (kns,s') form) theres where
  theres = [ s' | (s0,s') <- comknow kns ags, s0 == s ]
eval (kns,s) (Ckw ags form)  = alleqWith (\s' -> eval (kns,s') form) theres where
  theres = [ s' | (s0,s') <- comknow kns ags, s0 == s ]
eval scn (PubAnnounce form1 form2) =
  not (eval scn form1) || eval (pubAnnounceOnScn scn form1) form2
eval (kns,s) (PubAnnounceW form1 form2) =
  if eval (kns, s) form1
    then eval (pubAnnounce kns form1, s) form2
    else eval (pubAnnounce kns (Neg form1), s) form2
eval scn (Announce ags form1 form2) =
  not (eval scn form1) || eval (announceOnScn scn ags form1) form2
eval scn (AnnounceW ags form1 form2) =
  if eval scn form1
    then eval (announceOnScn scn ags form1      ) form2
    else eval (announceOnScn scn ags (Neg form1)) form2

pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOf kns psi)

pubAnnounceOnScn :: KnowScene -> Form -> KnowScene
pubAnnounceOnScn (kns,s) psi
  | eval (kns,s) psi = (pubAnnounce kns psi,s)
  | otherwise        = error "Liar!"

announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawbdd obs) ags psi = KnS newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con lawbdd (equ (var k) (bddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

announceOnScn :: KnowScene -> [Agent] -> Form -> KnowScene
announceOnScn (kns@(KnS props _ _),s) ags psi
  | eval (kns,s) psi = (announce kns ags psi, sort $ freshp props : s)
  | otherwise        = error "Liar!"

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
bddOf kns (PubAnnounce form1 form2) =
  imp (bddOf kns form1) (bddOf (pubAnnounce kns form1) form2)
bddOf kns (PubAnnounceW form1 form2) =
  ifthenelse (bddOf kns form1) newform2a newform2b where
    newform2a = bddOf (pubAnnounce kns form1) form2
    newform2b = bddOf (pubAnnounce kns (Neg form1)) form2

evalViaBdd :: KnowScene -> Form -> Bool
evalViaBdd (kns,s) f = evaluateFun (bddOf kns f) (\n -> P n `elem` s)

validViaBdd :: KnowStruct -> Form -> Bool
validViaBdd kns@(KnS _ lawbdd _) f = top == lawbdd `imp` bddOf kns f

whereViaBdd :: KnowStruct -> Form -> [State]
whereViaBdd kns@(KnS props lawbdd _) f =
 map (sort . map (toEnum . fst) . filter snd) $
   allSatsWith (map fromEnum props) $ con lawbdd (bddOf kns f)

type Propulation = Bdd

checkPropu :: Bdd -> KnowStruct -> KnowStruct -> Bool
checkPropu = undefined

data KnowTransf = KnT [Prp] Form [(Agent,[Prp])] deriving (Show)
type Event = (KnowTransf,State)

knowTransform :: KnowScene -> Event -> KnowScene
knowTransform (kns@(KnS props lawbdd obs),s) (KnT addprops addlaw eventobs, eventfacts) =
  (KnS (props ++ map snd shiftrel) newlawbdd newobs, s++shifteventfacts) where
    shiftrel = zip addprops [(freshp props)..]
    newobs = [ (i , sort $ apply obs i ++ map (apply shiftrel) (apply eventobs i)) | i <- map fst obs ]
    shiftaddlaw = replPsInF shiftrel addlaw
    newlawbdd = con lawbdd (bddOf kns shiftaddlaw)
    shifteventfacts = map (apply shiftrel) eventfacts

texBddWith :: (Int -> String) -> Bdd -> String
texBddWith myShow b = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  hPutStr i (genGraphWith myShow b ++ "\n")
  hClose i
  hGetContents o

texBDD :: Bdd -> String
texBDD = texBddWith show

instance TexAble KnowStruct where
  tex (KnS props lawbdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texBDD lawbdd
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> (tex os)) obs)
    , "\\end{array}\n"
    , " \\right)" ]

instance TexAble KnowScene where
  tex (kns, state) = tex kns ++ " , " ++ tex state

instance TexAble Event where
  tex (KnT props changelaw obs, actual) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , tex changelaw, "\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> (tex os)) obs)
    , "\\end{array}\n"
    , " \\right) , "
    , tex actual ]

pre :: Event -> Form
pre (KnT addprops changelaw _, x) = substitOutOf x addprops changelaw

reduce :: Event -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = pure $ Neg (pre e)
reduce e (PrpF p)     = Impl (pre e) <$> Just (PrpF p)
reduce e (Neg f)      = Impl (pre e) <$> (Neg <$> reduce e f)
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (pre e) <$> (Xor <$> mapM (reduce e) fs)
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce e@(t@(KnT addprops _ obs), x) (K a f) =
  Impl (pre e) <$> (Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME is this a bit much?
                             , seteq (restrictState x (obs ! a)) (restrictState y (obs ! a))
    ])
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ PubAnnounceW {} = Nothing
reduce _ Announce     {} = Nothing
reduce _ AnnounceW    {} = Nothing
