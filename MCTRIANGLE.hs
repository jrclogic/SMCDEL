
module MCTRIANGLE where

type State = (Int,Int)
data McModel = McM [State] [State] State deriving Show

mcModel :: State -> McModel
mcModel cur@(c,m) = McM ostates fstates cur where
  total   = c + m
  ostates = [ ((total-1)-m',m') | m'<-[0..(total-1)] ] -- observational states
  fstates = [ (total-m',    m') | m'<-[0..total    ] ] -- factual states

posFrom :: McModel -> State -> [State]
posFrom (McM _ fstates _) (oc,om) = filter (`elem` fstates) [ (oc+1,om), (oc,om+1) ]

obsFor :: McModel -> Bool -> State
obsFor (McM _ _ (curc,curm)) False = (curc-1,curm)
obsFor (McM _ _ (curc,curm)) True = (curc,curm-1)

posFor :: McModel -> Bool -> [State]
posFor m muddy = posFrom m $ obsFor m muddy

type Quantifier = State -> Bool

some :: Quantifier
some (_,b) = b > 0

data McFormula = Neg McFormula    -- negations
               | Conj [McFormula] -- conjunctions
               | Qf Quantifier    -- quantifiers
               | KnowSelf Bool    -- all b agents DO    know their status
               | NotKnowSelf Bool -- all b agents DON'T know their status

nobodyknows,everyoneKnows :: McFormula
nobodyknows   = Conj [ NotKnowSelf False, NotKnowSelf True ]
everyoneKnows = Conj [    KnowSelf False,    KnowSelf True ]

eval :: McModel -> McFormula -> Bool
eval m (Neg f)          = not $ eval m f
eval m (Conj fs)        = all (eval m) fs
eval (McM _ _ s) (Qf q) = q s
eval m@(McM _ _ (_,curm)) (KnowSelf    True ) = curm==0 || length (posFor m True ) == 1
eval m@(McM _ _ (curc,_)) (KnowSelf    False) = curc==0 || length (posFor m False) == 1
eval m@(McM _ _ (_,curm)) (NotKnowSelf True ) = curm==0 || length (posFor m True ) == 2
eval m@(McM _ _ (curc,_)) (NotKnowSelf False) = curc==0 || length (posFor m False) == 2

update :: McModel -> McFormula -> McModel
update (McM ostates fstates cur) f =
  McM ostates' fstates' cur where
    fstates' = filter (\s -> eval (McM ostates fstates s) f) fstates
    ostates' = filter (not . null . posFrom (McM [] fstates' cur)) ostates

step :: State -> Int -> McModel
step s 0 = update (mcModel s) (Qf some)
step s n = update (step s (n-1)) nobodyknows

showme :: State -> IO ()
showme s@(_,m) = mapM_ (\n -> putStrLn $ show n ++ ": " ++ show (step s n)) [0..(m-1)]
