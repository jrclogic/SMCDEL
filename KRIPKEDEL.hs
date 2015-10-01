
module KRIPKEDEL where
import Data.List (intercalate)
import DELLANG
import KRIPKEVIS
import HELP (alleq,fusion,apply)

type State = Int
type Partition = [[State]]
type Assignment = [(Prp,Bool)]
data KripkeModel = KrM [State] [(Agent,Partition)] [(State,Assignment)] deriving (Show)
type PointedModel = (KripkeModel,State)

eval :: PointedModel -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (KrM _ _ val, cur) (PrpF p) = apply (apply val cur) p
eval pm (Neg form)    = not $ eval pm form
eval pm (Conj forms)  = all (eval pm) forms
eval pm (Disj forms)  = any (eval pm) forms
eval pm (Xor  forms)  = odd $ length (filter id $ map (eval pm) forms)
eval pm (Impl f g)    = not (eval pm f) || eval pm g
eval pm (Equi f g)    = eval pm f == eval pm g
eval pm (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (m@(KrM _ rel _),w) (K ag form) = all (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrM _ rel _),w) (Kw ag form) = alleq (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrM _ rel _),w) (Ck ags form) = all (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) ckrel
  ckrel = fusion $ concat [ apply rel i | i <- ags ]
eval (m@(KrM _ rel _),w) (Ckw ags form) = alleq (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) ckrel
  ckrel = fusion $ concat [ apply rel i | i <- ags ]
eval pm (PubAnnounce form1 form2) =
  not (eval pm form1) || eval (pubAnnounce pm form1) form2
eval pm (PubAnnounceW form1 form2) =
  if eval pm form1
    then eval (pubAnnounce pm form1) form2
    else eval (pubAnnounce pm (Neg form1)) form2
eval pm (Announce ags form1 form2) =
  not (eval pm form1) || eval (announce pm ags form1) form2
eval pm (AnnounceW ags form1 form2) =
  if eval pm form1
    then eval (announce pm ags form1) form2
    else eval (announce pm ags (Neg form1)) form2

pubAnnounce :: PointedModel -> Form -> PointedModel
pubAnnounce pm@(m@(KrM sts rel val), cur) form =
  if eval pm form then (KrM newsts newrel newval, cur)
                  else error "pubAnnounce failed: Liar!"
  where
    newsts = filter (\s -> eval (m,s) form) sts
    nrel i = filter ([]/=) $ map (filter (`elem` newsts)) (apply rel i)
    newrel = [ (i, nrel i) | i <- map fst rel ]
    newval = filter (\p -> fst p `elem` newsts) val

announce :: PointedModel -> [Agent] -> Form -> PointedModel
announce pm@(m@(KrM sts rel val), cur) ags form =
  if eval pm form then (KrM newsts newrel newval, newcur)
                  else error "announce failed: Liar!"
  where
    tocopy = filter (\s -> eval (m,s) form) sts
    addsts = map (maximum sts +) [1..(length tocopy)]
    copyto = zip tocopy addsts
    copyof = zip addsts tocopy
    mapif  = concatMap (\s -> [apply copyto s | s `elem` tocopy])
    nrel i | i `elem` ags = apply rel i ++ filter ([]/=) (map mapif (apply rel i))
           | otherwise = map (\ec -> ec ++ mapif ec) (apply rel i)
    newsts = sts ++ addsts
    newrel = [ (i, nrel i) | i <- map fst rel ]
    newval = val ++ [ (s,apply val $ apply copyof s)  | s <- addsts ]
    newcur = apply copyto cur

showVal :: Assignment -> String
showVal ass = case filter snd ass of
  [] -> ""
  ps -> "$" ++ intercalate "," (map (texProp.fst) ps) ++ "$"

myDispModel :: PointedModel -> IO ()
myDispModel (KrM w r v, cur) = dispModel show id showVal "" (VisModel w r v cur)

myTexModel :: PointedModel -> String -> IO String
myTexModel (KrM w r v, cur) = texModel show id showVal "" (VisModel w r v cur)

data ActionModel = ActM [State] [(State,Form)] [(Agent,Partition)] deriving (Show)
type PointedActionModel = (ActionModel,State)

productUpdate :: PointedModel -> PointedActionModel -> PointedModel
productUpdate pm@(m@(KrM oldstates oldrel oldval), oldcur) (ActM actions precon actrel, faction) =
  let
    startcount        = maximum oldstates + 1
    copiesOf (s,a)    = [ (s, a, a * startcount + s) | eval (m, s) (apply precon a) ]
    newstatesTriples  = concat [ copiesOf (s,a) | s <- oldstates, a <- actions ]
    newstates         = map (\(_,_,x) -> x) newstatesTriples
    newval            = map (\(s,_,t) -> (t, apply oldval s)) newstatesTriples
    listFor ag        = cartProd (apply oldrel ag) (apply actrel ag)
    newPartsFor ag    = [ cartProd as bs | (as,bs) <- listFor ag ]
    translSingle pair = filter (`elem` newstates) $ map (\(_,_,x) -> x) $ copiesOf pair
    transEqClass      = concatMap translSingle
    nTransPartsFor ag = filter (\x-> x/=[]) $ map transEqClass (newPartsFor ag)
    newrel            = [ (a, nTransPartsFor a)  | a <- map fst oldrel ]
    ((_,_,newcur):_)  = copiesOf (oldcur,faction)
    factTest          = apply precon faction
    cartProd xs ys    = [ (x,y) | x <- xs, y <- ys ]
  in case ( map fst oldrel == map fst actrel, eval pm factTest ) of
    (False, _) -> error "productUpdate failed: Agents of KrM and ActM are not the same!"
    (_, False) -> error "productUpdate failed: Actual precondition is false!"
    _          -> (KrM newstates newrel newval, newcur)
