
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module SMCDEL.Explicit.Simple where
import Control.Arrow (second,(&&&))
import Data.List
import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Internal.Help (alleq,fusion,apply)

type State = Int

type Partition = [[State]]
type Assignment = [(Prp,Bool)]

data KripkeModel = KrM [State] [(Agent,Partition)] [(State,Assignment)] deriving (Eq,Ord,Show)
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
    newrel = map (second relfil) rel
    relfil = filter ([]/=) . map (filter (`elem` newsts))
    newval = filter (\p -> fst p `elem` newsts) val

announce :: PointedModel -> [Agent] -> Form -> PointedModel
announce pm@(m@(KrM sts rel val), cur) ags form =
  if eval pm form then (KrM sts newrel val, cur)
                  else error "announce failed: Liar!"
  where
    split ws = map sort.(\(x,y) -> [x,y]) $ partition ( \s -> eval (m,s) form) ws
    newrel = map nrel rel
    nrel (i,ri) | i `elem` ags = (i,filter ([]/=) (concatMap split ri))
                | otherwise    = (i,ri)

instance KripkeLike PointedModel where
  directed = const False
  getNodes (KrM ws _ val, _) = map (show &&& labelOf) ws where
    labelOf w = tex $ apply val w
  getEdges (KrM _ rel _, _) =
    nub $ concat $ concat $ concat [ [ [ [(a,show x,show y) | x<y] | x <- part, y <- part ] | part <- apply rel a ] | a <- map fst rel ]
  getActuals (KrM {}, cur) = [show cur]

instance TexAble PointedModel where tex = tex.ViaDot

data ActionModel = ActM [State] [(State,Form)] [(Agent,Partition)]
  deriving (Eq,Ord,Show)
type PointedActionModel = (ActionModel,State)

instance KripkeLike PointedActionModel where
  directed = const False
  getNodes (ActM as actval _, _) = map (show &&& labelOf) as where
    labelOf w = ppForm $ apply actval w
  getEdges (ActM _ _ rel, _) =
    nub $ concat $ concat $ concat [ [ [ [(a,show x,show y) | x<y] | x <- part, y <- part ] | part <- apply rel a ] | a <- map fst rel ]
  getActuals (ActM {}, cur) = [show cur]

instance TexAble PointedActionModel where tex = tex.ViaDot

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
