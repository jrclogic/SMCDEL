
module DELLANG where
import Data.List (nub,intercalate,(\\))
import Data.Maybe (fromJust)
import Test.QuickCheck

data Prp = P Int  deriving (Eq,Ord,Show)
instance Enum Prp where
  toEnum = P
  fromEnum (P n) = n

freshp :: [Prp] -> Prp
freshp [] = P 0
freshp prps = P (maximum (map fromEnum prps) + 1)

type Agent = String
alice,bob,carol :: Agent
alice   = "Alice"
bob     = "Bob"
carol   = "Carol"

data Form =
  Top | Bot | PrpF Prp | Neg Form | Conj [Form] | Disj [Form] | Xor [Form] |
  Impl Form Form | Equi Form Form | Forall [Prp] Form | Exists [Prp] Form |
  K Agent Form | Ck [Agent] Form | Kw Agent Form | Ckw [Agent] Form |
  PubAnnounce Form Form | PubAnnounceW Form Form |
  Announce [Agent] Form Form | AnnounceW [Agent] Form Form
  deriving (Eq,Ord,Show)

pubAnnounceStack :: [Form] -> Form -> Form
pubAnnounceStack = flip $ foldr PubAnnounce

pubAnnounceWhetherStack :: [Form] -> Form -> Form
pubAnnounceWhetherStack = flip $ foldr PubAnnounceW

booloutofForm :: [Prp] -> [Prp] -> Form
booloutofForm ps qs = Conj $ [ PrpF p | p <- ps ] ++ [ Neg $ PrpF r | r <- qs \\ ps ]

substit :: Prp -> Form -> Form -> Form
substit _ _   Top           = Top
substit _ _   Bot           = Bot
substit q psi (PrpF p)      = if p==q then psi else PrpF p
substit q psi (Neg form)    = Neg (substit q psi form)
substit q psi (Conj forms)  = Conj (map (substit q psi) forms)
substit q psi (Disj forms)  = Disj (map (substit q psi) forms)
substit q psi (Xor  forms)  = Xor  (map (substit q psi) forms)
substit q psi (Impl f g)    = Impl (substit q psi f) (substit q psi g)
substit q psi (Equi f g)    = Equi (substit q psi f) (substit q psi g)
substit q psi (Forall ps f) = if q `elem` ps
  then error ("substit failed: Substituens "++ show q ++ " in 'Forall " ++ show ps)
  else Forall ps (substit q psi f)
substit q psi (Exists ps f) = if q `elem` ps
  then error ("substit failed: Substituens " ++ show q ++ " in 'Exists " ++ show ps)
  else Exists ps (substit q psi f)
substit q psi (K  i f)     = K  i (substit q psi f)
substit q psi (Kw i f)     = Kw i (substit q psi f)
substit q psi (Ck ags f)   = Ck ags (substit q psi f)
substit q psi (Ckw ags f)  = Ckw ags (substit q psi f)
substit q psi (PubAnnounce f g)   = PubAnnounce (substit q psi f) (substit q psi g)
substit q psi (PubAnnounceW f g)  = PubAnnounceW (substit q psi f) (substit q psi g)
substit q psi (Announce ags f g)  = Announce ags (substit q psi f) (substit q psi g)
substit q psi (AnnounceW ags f g) = AnnounceW ags (substit q psi f) (substit q psi g)

substitSet :: [(Prp,Form)] -> Form -> Form
substitSet [] f = f
substitSet ((q,psi):rest) f = substitSet rest (substit q psi f)

replPsInF :: [(Prp,Prp)] -> Form -> Form
replPsInF _       Top      = Top
replPsInF _       Bot      = Bot
replPsInF repl (PrpF p)    | p `elem` map fst repl = PrpF (fromJust $ lookup p repl)
                           | otherwise = PrpF p
replPsInF repl (Neg f)     = Neg $ replPsInF repl f
replPsInF repl (Conj fs)   = Conj $ map (replPsInF repl) fs
replPsInF repl (Disj fs)   = Disj $ map (replPsInF repl) fs
replPsInF repl (Xor  fs)   = Xor  $ map (replPsInF repl) fs
replPsInF repl (Impl f g)  = Impl (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Equi f g)  = Equi (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Forall ps f) = Forall (map (fromJust . flip lookup repl) ps) (replPsInF repl f)
replPsInF repl (Exists ps f) = Exists (map (fromJust . flip lookup repl) ps) (replPsInF repl f)
replPsInF repl (K i f)     = K i (replPsInF repl f)
replPsInF repl (Kw i f)    = Kw i (replPsInF repl f)
replPsInF repl (Ck ags f)  = Ck ags (replPsInF repl f)
replPsInF repl (Ckw ags f) = Ckw ags (replPsInF repl f)
replPsInF repl (PubAnnounce f g)   = PubAnnounce   (replPsInF repl f) (replPsInF repl g)
replPsInF repl (PubAnnounceW f g)  = PubAnnounceW  (replPsInF repl f) (replPsInF repl g)
replPsInF repl (Announce ags f g)  = Announce  ags (replPsInF repl f) (replPsInF repl g)
replPsInF repl (AnnounceW ags f g) = AnnounceW ags (replPsInF repl f) (replPsInF repl g)

propsInForm :: Form -> [Prp]
propsInForm Top                = []
propsInForm Bot                = []
propsInForm (PrpF p)           = [p]
propsInForm (Neg f)            = propsInForm f
propsInForm (Conj fs)          = nub $ concatMap propsInForm fs
propsInForm (Disj fs)          = nub $ concatMap propsInForm fs
propsInForm (Xor  fs)          = nub $ concatMap propsInForm fs
propsInForm (Impl f g)         = nub $ concatMap propsInForm [f,g]
propsInForm (Equi f g)         = nub $ concatMap propsInForm [f,g]
propsInForm (Forall ps f)      = nub $ ps ++ propsInForm f
propsInForm (Exists ps f)      = nub $ ps ++ propsInForm f
propsInForm (K _ f)            = propsInForm f
propsInForm (Kw _ f)           = propsInForm f
propsInForm (Ck _ f)           = propsInForm f
propsInForm (Ckw _ f)          = propsInForm f
propsInForm (Announce _ f g)   = nub $ propsInForm f ++ propsInForm g
propsInForm (AnnounceW _ f g)  = nub $ propsInForm f ++ propsInForm g
propsInForm (PubAnnounce f g)  = nub $ propsInForm f ++ propsInForm g
propsInForm (PubAnnounceW f g) = nub $ propsInForm f ++ propsInForm g

propsInForms :: [Form] -> [Prp]
propsInForms fs = nub $ concatMap propsInForm fs

texProp :: Prp -> String
texProp (P 0) = " p "
texProp (P n) = " p_{" ++ show n ++ "} "

texPropSet :: [Prp] -> String
texPropSet [] = " \\varnothing "
texPropSet ps = "\\{" ++ intercalate "," (map texProp ps) ++ "\\}"

simplify :: Form -> Form
simplify f = if simStep f == f then f else simplify (simStep f)

simStep :: Form -> Form
simStep Top           = Top
simStep Bot           = Bot
simStep (PrpF p)      = PrpF p
simStep (Neg Top)     = Bot
simStep (Neg Bot)     = Top
simStep (Neg (Neg f)) = simStep f
simStep (Neg f)       = Neg $ simStep f
simStep (Conj [])     = Top
simStep (Conj [f])    = simStep f
simStep (Conj fs)     | Bot `elem` fs = Bot
                      | otherwise     = Conj (nub $ map simStep (filter (Top /=) fs))
simStep (Disj [])     = Bot
simStep (Disj [f])    = simStep f
simStep (Disj fs)     | Top `elem` fs = Top
                      | otherwise     = Disj (nub $ map simStep (filter (Bot /=) fs))
simStep (Xor  [])     = Bot
simStep (Xor  [f])    = Neg $ simStep f
simStep (Xor  fs)     = Xor (map simStep fs)
simStep (Impl Bot _)  = Top
simStep (Impl _ Top)  = Top
simStep (Impl Top f)  = simStep f
simStep (Impl f Bot)  = Neg (simStep f)
simStep (Impl f g)    = Impl (simStep f) (simStep g)
simStep (Equi Top f)  = simStep f
simStep (Equi Bot f)  = Neg (simStep f)
simStep (Equi f Top)  = simStep f
simStep (Equi f Bot)  = Neg (simStep f)
simStep (Equi f g)    = Equi (simStep f) (simStep g)
simStep (Forall ps f) = Forall ps (simStep f)
simStep (Exists ps f) = Exists ps (simStep f)
simStep (K a f)       = K a (simStep f)
simStep (Kw a f)      = Kw a (simStep f)
simStep (Ck ags f)    = Ck ags (simStep f)
simStep (Ckw ags f)   = Ckw ags (simStep f)
simStep (PubAnnounce Top f) = simStep f
simStep (PubAnnounce Bot _) = Top
simStep (PubAnnounce  f g)  = PubAnnounce  (simStep f) (simStep g)
simStep (PubAnnounceW f g)  = PubAnnounceW (simStep f) (simStep g)
simStep (Announce  ags f g) = Announce  ags (simStep f) (simStep g)
simStep (AnnounceW ags f g) = AnnounceW ags (simStep f) (simStep g)

texForm :: Form -> String
texForm Top           = "\\top "
texForm Bot           = "\\bot "
texForm (PrpF p)      = texProp p
texForm (Neg (PubAnnounce f (Neg g))) = "\\langle !" ++ texForm f ++ " \\rangle " ++ texForm g
texForm (Neg f)       = "\\lnot " ++ texForm f
texForm (Conj [])     = "\\top "
texForm (Conj [f])    = texForm f
texForm (Conj [f,g])  = " ( " ++ texForm f ++ " \\land " ++ texForm g ++" ) "
texForm (Conj fs)     = "\\bigwedge \\{\n" ++ intercalate "," (map texForm fs) ++" \\} "
texForm (Disj [])     = "\\bot "
texForm (Disj [f])    = texForm f
texForm (Disj [f,g])  = " ( " ++ texForm f ++ " \\lor "++ texForm g ++ " ) "
texForm (Disj fs)     = "\\bigvee \\{\n " ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Xor [])      = "\\bot "
texForm (Xor [f])     = texForm f
texForm (Xor [f,g])   = " ( " ++ texForm f  ++ " \\oplus " ++ texForm g ++ " ) "
texForm (Xor fs)      = "\\bigoplus \\{\n" ++ intercalate "," (map texForm fs) ++ " \\} "
texForm (Equi f g)    = " ( "++ texForm f ++" \\leftrightarrow "++ texForm g ++" ) "
texForm (Impl f g)    = " ( "++ texForm f ++" \\rightarrow "++ texForm g ++" ) "
texForm (Forall ps f) = " \\forall " ++ texPropSet ps ++ " " ++ texForm f
texForm (Exists ps f) = " \\exists " ++ texPropSet ps ++ " " ++ texForm f
texForm (K i f)       = "K_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Kw i f)      = "K^?_{\\text{" ++ i ++ "}} " ++ texForm f
texForm (Ck ags f)    = "Ck_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (Ckw ags f)   = "Ck^?_{\\{\n" ++ intercalate "," ags ++ "\n\\}} " ++ texForm f
texForm (PubAnnounce f g)   = "[!" ++ texForm f ++ "] " ++ texForm g
texForm (PubAnnounceW f g)  = "[?!" ++ texForm f ++ "] " ++ texForm g
texForm (Announce ags f g)  = "[" ++ intercalate "," ags ++ "!" ++ texForm f ++ "] " ++ texForm g
texForm (AnnounceW ags f g) = "[" ++ intercalate "," ags ++ "?!" ++ texForm f ++ "] " ++ texForm g

testForm :: Form
testForm = Forall [P 3] $ Equi (Disj [Bot,PrpF $ P 3,Bot]) (Conj [Top,Xor [Top,Kw alice (PrpF (P 4))], AnnounceW [alice,bob] (PrpF (P 5)) (Kw bob $ PrpF (P 5))  ])

data BF = BF Form deriving (Eq,Ord,Show)

instance Arbitrary BF where
  arbitrary = sized randomboolform

randomboolform ::  Int -> Gen BF
randomboolform sz = BF <$> bf' sz' where
  maximumvar = 1000
  sz' = min maximumvar sz
  bf' 0 = (PrpF . P) <$> choose (0, sz')
  bf' n = oneof [ pure DELLANG.Top
                , pure DELLANG.Bot
                , (PrpF . P) <$> choose (0, sz')
                , Neg <$> st
                , (\x y -> Conj [x,y]) <$> st <*> st
                , (\x y -> Disj [x,y]) <$> st <*> st
                , Impl <$> st <*> st
                , Equi <$> st <*> st
                , (\x y -> Xor [x,y]) <$> st <*> st
                , (\m f -> Exists [P m] f) <$> choose (0, maximumvar) <*> st
                , (\m f -> Forall [P m] f) <$> randomvar <*> st
                ]
    where
      st = bf' (n `div` 2)
      randomvar = elements [0..maximumvar]
