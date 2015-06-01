
module SAP where
import Data.List
import Data.Maybe
import KNSCAC
import DELLANG (Prp(..),Form(PrpF,Kw),Form,Agent)
import qualified DELLANG
import Data.HasCacBDD hiding (Var)
import Data.HasCacBDD.Visuals

globalMaximum :: Int
globalMaximum = 100*100

digits :: Int
digits = ceiling $ logBase (2::Double) (fromIntegral globalMaximum)

variables :: Int
variables = 4

data NnVar = N Int
  deriving (Ord,Eq,Show)

instance Enum NnVar where
  fromEnum (N k) = k
  toEnum = N

propsFor :: NnVar -> [Prp]
propsFor (N k) = map (P . (\n -> variables*n +k)) [0..(digits-1)] -- interleaved!

allprops :: [Prp]
allprops = map P [0..(digits*variables-1)]

data NnTerm = Abs Int | Var NnVar | Sum NnTerm NnTerm | Product NnTerm NnTerm
  deriving (Ord,Eq,Show)

data NnForm = Equal NnTerm NnTerm | Lower NnTerm NnTerm
  deriving (Ord,Eq,Show)

nnt2delfObdds :: NnTerm -> [Bdd]
nnt2delfObdds (Abs n)       = take digits (decToObdd n ++ repeat bot)
nnt2delfObdds (Var (N k))   = [ var n | (P n) <- propsFor (N k) ]
nnt2delfObdds (Sum s t)     = binSum  (nnt2delfObdds s) (nnt2delfObdds t)
nnt2delfObdds (Product s t) = binProd (nnt2delfObdds s) (nnt2delfObdds t)

nnf2delfObdd :: NnForm -> Bdd
nnf2delfObdd (Equal u v) = conSet $ zipWith equ (nnt2delfObdds u) (nnt2delfObdds v)
nnf2delfObdd (Lower u v) = binLow pairlist
  where -- we need the most significant digit first!
    pairlist = reverse $ zip (nnt2delfObdds u) (nnt2delfObdds v)
    binLow []           = bot
    binLow ((x,y):rest) =
      dis
	(con (neg x) y)
	(con (equ x y) (binLow rest))

decToObdd :: Int -> [Bdd]
decToObdd 0 = [bot]
decToObdd y = let (a,b) = quotRem y 2 in binsymbol b : decToObdd a
  where
    binsymbol 0 = bot
    binsymbol _ = top

binToDec :: [Bool] -> Int
binToDec bs = sum [ fromEnum b * (2 ^ n) | (b,n) <- zip bs [(0::Int)..] ]

-- NB: this takes the least significant digit first!
binSum :: [Bdd] -> [Bdd] -> [Bdd]
binSum fs gs = [ fst $ result k | k <- [1..digits] ] where
  result 1 = ( xor (f 1) (g 1), con (f 1) (g 1) ) -- (here, carryover)
  result k = ( xor (xor (f k) (g k)) (co k) , disSet [ con (f k) (g k), con (f k) (co k), con (g k) (co k) ] )
  f n  = fst $ last $ take n (zip fs gs)
  g n  = snd $ last $ take n (zip fs gs)
  co n = snd $ result (n-1) -- this is the induction.

-- NB: this takes the least significant digit first!
binProd :: [Bdd] -> [Bdd] -> [Bdd]
binProd fs gs = foldl binSum l ls where
  (l:ls) = [ sumLine k | k <- [1..digits] ]
  sumLine i = take digits $ replicate (i-1) bot ++ map (con (g i) . f) [1..digits]
  f n = fst $ last $ take n (zip fs gs)
  g n = snd $ last $ take n (zip fs gs)

testArithmetic :: [Bool]
testArithmetic = concat [ results (n::Int) | n <- [1..5] ] where
  results 1 = map
    (\x -> top == nnf2delfObdd (Equal (Abs x) (Abs x)))
    ([93,20,23,204,2015,16383,123]::[Int])
  results 2 = map
    (\(x,y) ->  top == nnf2delfObdd (Equal (Sum (Abs x) (Abs y)) (Abs $ x + y) ))
    (zip [2,6,102,298,1223,512] [93,20,23,204,2015,16383,123])
  results 3 = map
    (\(x,y) -> top == nnf2delfObdd (Equal (Product (Abs x) (Abs y)) (Abs $ x * y) ))
    (zip [5..23] [21..47])
  results 4 = map
    (\(x,y) -> top == nnf2delfObdd (Lower (Abs x) (Abs y) ))
    (zip [1..45] [55..100])
  results _ = map
    (\(x,y) -> bot == nnf2delfObdd (Lower (Abs x) (Abs y) ))
    (zip [55..100] [1..45])

type FormOrBddAtom = Either Form Bdd

data FormOrBdd = Atom FormOrBddAtom | Neg FormOrBdd |
  Conj [FormOrBdd] | Disj [FormOrBdd] | Xor [FormOrBdd] |
  Impl FormOrBdd FormOrBdd | Equi FormOrBdd FormOrBdd |
  Forall [Prp] FormOrBdd | Exists [Prp] FormOrBdd |
  K Agent FormOrBdd | Ck [Agent] FormOrBdd |
  PubAnnounce FormOrBdd FormOrBdd | Announce [Agent] FormOrBdd FormOrBdd

bddOfMixed :: KnowStruct -> FormOrBdd -> Bdd
bddOfMixed _   (Atom (Right b)) = b
bddOfMixed kns (Atom (Left  f)) = bddOf kns f

bddOfMixed kns (Neg form)    = neg $ bddOfMixed kns form
bddOfMixed kns (Conj forms)  = conSet $ map (bddOfMixed kns) forms
bddOfMixed kns (Disj forms)  = disSet $ map (bddOfMixed kns) forms
bddOfMixed kns (Xor  forms)  = xorSet $ map (bddOfMixed kns) forms
bddOfMixed kns (Impl f g)    = imp (bddOfMixed kns f) (bddOfMixed kns g)
bddOfMixed kns (Equi f g)    = equ (bddOfMixed kns f) (bddOfMixed kns g)
bddOfMixed kns (Forall ps f) = forallSet (map fromEnum ps) (bddOfMixed kns f)
bddOfMixed kns (Exists ps f) = existsSet (map fromEnum ps) (bddOfMixed kns f)
bddOfMixed kns@(KnS allpropshere lawbdd obs) (K i form) =
  forallSet otherps (imp lawbdd (bddOfMixed kns form)) where
    otherps = map (\(P n) -> n) $ allpropshere \\ fromJust (lookup i obs)
bddOfMixed kns@(KnS allpropshere lawbdd obs) (Ck ags form) = gfp lambda where
  lambda z = conSet $ bddOfMixed kns form : [ forallSet (otherps i) (imp lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allpropshere \\ fromJust (lookup i obs)
bddOfMixed _   (Announce {}) = error "bddOfMixed failed: 'Announce' not implemented."
bddOfMixed kns (PubAnnounce form1 form2) = imp (bddOfMixed kns form1) newform2 where
    newform2 = bddOfMixed (pubAnnounceMixed kns form1) form2

pubAnnounceMixed :: KnowStruct -> FormOrBdd -> KnowStruct
pubAnnounceMixed kns@(KnS props lawbdd obs) psi = KnS props newlawbdd obs where
  newlawbdd = con lawbdd (bddOfMixed kns psi)

validViaBddMixed :: KnowStruct -> FormOrBdd -> Bool
validViaBddMixed kns@(KnS _ lawbdd _) f = top == imp lawbdd (bddOfMixed kns f)

evalViaBddMixed :: Scenario -> FormOrBdd -> Bool
evalViaBddMixed (kns@(KnS allpropshere _ _),s) f = bool where
  bool = b==top || b /= bot && error "evalViaBdd failed: Composite BDD leftover."
  b    = restrictSet (bddOfMixed kns f) list
  list = [ (n,True) | (P n) <- s ] ++ [ (n,False) | (P n) <- allpropshere \\ s ]

toyInit :: KnowStruct
toyInit = KnS
  allprops
  top -- no conditions
  [ (0,[]), (1,[]) ]

toyForm :: FormOrBdd
toyForm =
  PubAnnounce -- announce that N0 = 10
    ( Atom $ Right $ nnf2delfObdd $ Equal (Var (N 0)) (Abs 10) )
    (PubAnnounce -- announce that N0 = N1
      ( Atom $ Right $ nnf2delfObdd $ Equal (Var (N 0)) (Var (N 1)) )
      -- Now 0 knows that N1 = 10
      ( K 0 $ Atom $ Right $ nnf2delfObdd $ Equal (Var (N 1)) (Abs 10) )
    )

toyCheck :: Bool
toyCheck = top == bddOfMixed toyInit toyForm

toy2Init :: KnowStruct
toy2Init = KnS
  allprops
  (conSet [
    nnf2delfObdd $ Lower (Abs 1)                           (Var (N 0)), --  1 < N0
    nnf2delfObdd $ Lower (Var (N 0))                       (Var (N 1)), -- N0 < N1
    nnf2delfObdd $ Lower (Var (N 0))                       (Abs 101)  , -- N0 < 101
    nnf2delfObdd $ Lower (Var (N 1))                       (Abs 101)    -- N1 < 101
  ] )
  [ (0,[]), (1,propsFor (N 3)) ]

toy2Form :: Int -> FormOrBdd
toy2Form z =
  Impl
    (Atom $ Right $ nnf2delfObdd $ Equal (Var (N 3)) (Abs z))
    (PubAnnounce -- announce that N0*N1=N3
      (Atom $ Right $nnf2delfObdd $ Equal (Product (Var (N 0)) (Var (N 1))) (Var (N 3)) )
      -- Now 1 knows N1
      (Atom $ Left $ knowsThis 1 (N 1) )
    )

toy2Check :: Bool
toy2Check = top == bddOfMixed toy2Init (toy2Form 21)

-- the order here seems to matter, also the AndSet implementation seems bad
sapConditions :: Bdd
sapConditions = conSet [
  nnf2delfObdd $ Lower (Var (N 0))                       (Abs 101)  , -- N0      < 101
  nnf2delfObdd $ Lower (Var (N 1))                       (Abs 101)  , -- N1      < 101
  nnf2delfObdd $ Lower (Abs 1)                           (Var (N 0)), --  1      < N0
  nnf2delfObdd $ Lower (Var (N 0))                       (Var (N 1)), -- N0      < N1
  nnf2delfObdd $ Lower (Sum (Var (N 0)) (Var (N 1)))     (Abs 101)  , -- N0 + N1 < 101
  nnf2delfObdd $ Equal (Sum (Var (N 0)) (Var (N 1)))     (Var (N 2)), -- N0 + N1 = N2
  nnf2delfObdd $ Equal (Product (Var (N 0)) (Var (N 1))) (Var (N 3))  -- N0 * N1 = N3
  ]

sapInit :: KnowStruct
sapInit = KnS
  allprops
  sapConditions
  [ (0,propsFor (N 2)), (1,propsFor (N 3)) ]

knowsThis :: Agent -> NnVar -> Form
knowsThis i (N n) =
  DELLANG.Conj [ Kw i (PrpF p) | p <- propsFor (N n) ]

knowsThePair :: Agent -> FormOrBdd
knowsThePair i = Atom $ Left $ DELLANG.Conj [knowsThis i (N 0), knowsThis i (N 1) ]

sapState :: (Int,Int) -> [Prp]
sapState (a,b) = map (P . fst) $ filter snd fulldesc where
  fulldesc = case length sats of
    0 -> error "no solution!"
    1 -> head sats
    _ -> error "too many solutions!"
  sats = allSats ( -- fail hard if we have more or less than one solution!
    con sapConditions $ conSet [
      nnf2delfObdd $ Equal (Var (N 0)) (Abs a),
      nnf2delfObdd $ Equal (Var (N 1)) (Abs b),
      nnf2delfObdd $ Equal (Var (N 2)) (Abs $ a+b),
      nnf2delfObdd $ Equal (Var (N 3)) (Abs $ a*b)
      ] )

sapValuesAtState :: [Prp] -> [(NnVar,Int)]
sapValuesAtState state = [ (v,val v) | v <- [N 0..N (variables-1)] ] where
  val v =  binToDec $ map (`elem` state) (propsFor v)

sapResult :: (Int,Int) -> Bdd
sapResult (a,b) = con
  ( nnf2delfObdd $ Equal (Var (N 0)) (Abs a) )
  ( nnf2delfObdd $ Equal (Var (N 1)) (Abs b) )

sapForm :: FormOrBdd
sapForm = Equi
  (Atom $ Right $ sapResult (3,14)) -- The result is (3,14) iff
  (Conj [
    K 0 (Neg $ knowsThePair 1 ),    --   i) Sum knows that Product does not know x and y,
    PubAnnounce                     --  ii) After announcing this, Product knows the pair and
      (K 0 (Neg $ knowsThePair 1 ))
      (knowsThePair 1),
    PubAnnounce                     -- iii) after announcing that, Sum knows the pair.
      (K 0 (Neg $ knowsThePair 1 ))
      (PubAnnounce (knowsThePair 1) (knowsThePair 0))
  ])

sapCheck :: Bool
sapCheck = validViaBddMixed sapInit sapForm -- TODO: wrong result!

sapForms :: [(String,FormOrBdd)]
sapForms = [
  ("The sum is 3 + 14 = 17", Atom $ Right (nnf2delfObdd $ Equal (Var (N 2)) (Abs $ 3+14)) ),
  ("The product is 3 * 14 = 42", Atom $ Right (nnf2delfObdd $ Equal (Var (N 3)) (Abs $ 3*14)) ),
  ("Product does not know (x,y)",Neg $ knowsThePair 1),
  ("Sum knows this",K 0 (Neg $ knowsThePair 1 )),
  ("After announcing this, Product knows (x,y)", -- TODO: wrong result!
    PubAnnounce
      (K 0 (Neg $ knowsThePair 1 ))
      (knowsThePair 1)
    ),
  ("After announcing that, Sum knows the pair",
    PubAnnounce
      (K 0 (Neg $ knowsThePair 1 ))
      (PubAnnounce
	(knowsThePair 1)
	(knowsThePair 0)
      )
    )
  ]

sapDebug :: IO ()
sapDebug = do
  putStrLn "At state (3,14):"
  mapM_ (\(t,f) -> putStrLn $ t ++ ": " ++ show (evalViaBddMixed (sapInit,sapState (3,14)) f)) sapForms

view :: Bdd -> IO ()
view = showGraph
