{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module SMCDEL.Explicit.S5 where
import Control.Arrow (second,(&&&))
import Data.GraphViz
import Data.List
import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Internal.Help (alleqWith,fusion,apply,(!),lfp)
import Test.QuickCheck

type World = Int

class HasWorlds a where
  worldsOf :: a -> [World]

type Partition = [[World]]
type Assignment = [(Prp,Bool)]

data KripkeModelS5 = KrMS5 [World] [(Agent,Partition)] [(World,Assignment)] deriving (Eq,Ord,Show)
type PointedModelS5 = (KripkeModelS5,World)

instance HasAgents KripkeModelS5 where
  agentsOf (KrMS5 _ rel _) = map fst rel

instance HasAgents PointedModelS5 where
  agentsOf = agentsOf . fst

instance HasVocab KripkeModelS5 where
  vocabOf (KrMS5 _ _ val) = map fst $ snd (head val)

instance HasVocab PointedModelS5 where
  vocabOf = vocabOf . fst

instance HasWorlds KripkeModelS5 where
  worldsOf (KrMS5 ws _ _) = ws

instance HasWorlds PointedModelS5 where
  worldsOf = worldsOf . fst

newtype PropList = PropList [Prp]

withoutWorld :: KripkeModelS5 -> World -> KripkeModelS5
withoutWorld (KrMS5 worlds parts val) w = KrMS5
  (delete w worlds)
  (map (second (filter (/=[]) . map (delete w))) parts)
  (filter ((/=w).fst) val)

withoutProps :: KripkeModelS5 -> [Prp] -> KripkeModelS5
withoutProps (KrMS5 worlds parts val) dropProps = KrMS5
  worlds
  parts
  (map (second $ filter ((`notElem` dropProps) . fst)) val)

instance Arbitrary PropList where
  arbitrary = do
    moreprops <- sublistOf (map P [1..10])
    return $ PropList $ P 0 : moreprops

randomPartFor :: [World] -> Gen Partition
randomPartFor worlds = do
  indices <- infiniteListOf $ choose (1, length worlds)
  let pairs = zip worlds indices
  let parts = [ sort $ map fst $ filter ((==k).snd) pairs | k <- [1 .. (length worlds)] ]
  return $ sort $ filter (/=[]) parts

instance Arbitrary KripkeModelS5 where
  arbitrary = do
    let agents = map show [1..(5::Int)]
    let props = map P [0..4]
    worlds <- sort . nub <$> listOf1 (elements [0..8])
    val <- mapM (\w -> do
      randomAssignment <- zip props <$> infiniteListOf (choose (True,False))
      return (w,randomAssignment)
      ) worlds
    parts <- mapM (\i -> do
      randomPartition <- randomPartFor worlds
      return (i,randomPartition)
      ) agents
    return $ KrMS5 worlds parts val
  shrink m@(KrMS5 worlds _ _) =
    [ m `withoutWorld` w | w <- worlds, length worlds > 1 ]

eval :: PointedModelS5 -> Form -> Bool
eval _ Top = True
eval _ Bot = False
eval (KrMS5 _ _ val, cur) (PrpF p) = apply (apply val cur) p
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
eval (m@(KrMS5 _ rel _),w) (K ag form) = all (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrMS5 _ rel _),w) (Kw ag form) = alleqWith (\w' -> eval (m,w') form) vs where
  vs = concat $ filter (elem w) (apply rel ag)
eval (m@(KrMS5 _ rel _),w) (Ck ags form) = all (\w' -> eval (m,w') form) vs where
  vs    = concat $ filter (elem w) ckrel
  ckrel = fusion $ concat [ apply rel i | i <- ags ]
eval (m@(KrMS5 _ rel _),w) (Ckw ags form) = alleqWith (\w' -> eval (m,w') form) vs where
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

valid :: KripkeModelS5 -> Form -> Bool
valid m@(KrMS5 worlds _ _) f = all (\w -> eval (m,w) f) worlds

pubAnnounce :: PointedModelS5 -> Form -> PointedModelS5
pubAnnounce pm@(m@(KrMS5 sts rel val), cur) form =
  if eval pm form then (KrMS5 newsts newrel newval, cur)
                  else error "pubAnnounce failed: Liar!"
  where
    newsts = filter (\s -> eval (m,s) form) sts
    newrel = map (second relfil) rel
    relfil = filter ([]/=) . map (filter (`elem` newsts))
    newval = filter (\p -> fst p `elem` newsts) val

announce :: PointedModelS5 -> [Agent] -> Form -> PointedModelS5
announce pm@(m@(KrMS5 sts rel val), cur) ags form =
  if eval pm form then (KrMS5 sts newrel val, cur)
                  else error "announce failed: Liar!"
  where
    split ws = map sort.(\(x,y) -> [x,y]) $ partition (\s -> eval (m,s) form) ws
    newrel = map nrel rel
    nrel (i,ri) | i `elem` ags = (i,filter ([]/=) (concatMap split ri))
                | otherwise    = (i,ri)

instance KripkeLike KripkeModelS5 where
  directed = const False
  getNodes (KrMS5 ws _ val) = map (show &&& labelOf) ws where
    labelOf w = tex $ apply val w
  getEdges (KrMS5 _ rel _) =
    nub [ (a,show x,show y) | a <- map fst rel, part <- apply rel a, x <- part, y <- part, x < y ]

instance KripkeLike PointedModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, cur) = [show cur]

instance TexAble PointedModelS5 where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

type Bisimulation = [(World,World)]

checkBisim :: Bisimulation -> KripkeModelS5 -> KripkeModelS5 -> Bool
checkBisim [] _                   _                     = False
checkBisim z  m1@(KrMS5 _ rel1 val1) m2@(KrMS5 _ rel2 val2) =
     all (\(w1,w2) -> val1 ! w1 == val2 ! w2) z -- same props
  && and [ any (\v2 -> (v1,v2) `elem` z) (concat $ filter (elem w2) (rel2 ! ag)) -- forth
         | (w1,w2) <- z, ag <- agentsOf m1, v1 <- concat $ filter (elem w1) (rel1 ! ag) ]
  && and [ any (\v1 -> (v1,v2) `elem` z) (concat $ filter (elem w1) (rel1 ! ag)) -- back
         | (w1,w2) <- z, ag <- agentsOf m2, v2 <- concat $ filter (elem w2) (rel2 ! ag) ]

generatedSubmodel :: PointedModelS5 -> PointedModelS5
generatedSubmodel (KrMS5 _ rel val, cur) = (KrMS5 newWorlds newrel newval, cur) where
  newWorlds :: [World]
  newWorlds = lfp follow [cur] where
    follow xs = sort . nub $ concat [ part | (_,parts) <- rel, part <- parts, any (`elem` part) xs ]
  newrel = map (second $ filter (any (`elem` newWorlds))) rel
  newval = filter (\p -> fst p `elem` newWorlds) val

type Action = Int
data ActionModel = ActM [Action] [(Action,Form)] [(Agent,Partition)]
  deriving (Eq,Ord,Show)
type PointedActionModel = (ActionModel,Action)

instance KripkeLike PointedActionModel where
  directed = const False
  getNodes (ActM as actval _, _) = map (show &&& labelOf) as where
    labelOf w = " $ ? " ++ tex (apply actval w) ++ " $ "
  getEdges (ActM _ _ rel, _) =
    nub [ (a, show x, show y) | a <- map fst rel, part <- apply rel a, x <- part, y <- part, x < y ]
  getActuals (ActM {}, cur) = [show cur]
  nodeAts _ True  = [shape BoxShape, style solid]
  nodeAts _ False = [shape BoxShape, style dashed]

instance TexAble PointedActionModel where tex = tex.ViaDot

instance Arbitrary ActionModel where
  arbitrary = do
    f <- arbitrary
    g <- arbitrary
    h <- arbitrary
    return $
      ActM [0..3] [(0,Top),(1,f),(2,g),(3,h)] ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3::Int]]) | k<-[1..5::Int] ])

productUpdate :: PointedModelS5 -> PointedActionModel -> PointedModelS5
productUpdate pm@(m@(KrMS5 oldWorlds oldrel oldval), oldcur) (ActM actions precon actrel, faction) =
  let
    startcount        = maximum oldWorlds + 1
    copiesOf (s,a)    = [ (s, a, a * startcount + s) | eval (m, s) (apply precon a) ]
    newWorldsTriples  = concat [ copiesOf (s,a) | s <- oldWorlds, a <- actions ]
    newWorlds         = map (\(_,_,x) -> x) newWorldsTriples
    newval            = map (\(s,_,t) -> (t, apply oldval s)) newWorldsTriples
    listFor ag        = cartProd (apply oldrel ag) (apply actrel ag)
    newPartsFor ag    = [ cartProd as bs | (as,bs) <- listFor ag ]
    translSingle pair = filter (`elem` newWorlds) $ map (\(_,_,x) -> x) $ copiesOf pair
    transEqClass      = concatMap translSingle
    nTransPartsFor ag = filter (\x-> x/=[]) $ map transEqClass (newPartsFor ag)
    newrel            = [ (a, nTransPartsFor a)  | a <- map fst oldrel ]
    ((_,_,newcur):_)  = copiesOf (oldcur,faction)
    factTest          = apply precon faction
    cartProd xs ys    = [ (x,y) | x <- xs, y <- ys ]
  in case ( map fst oldrel == map fst actrel, eval pm factTest ) of
    (False, _) -> error "productUpdate failed: Agents of KrMS5 and ActM are not the same!"
    (_, False) -> error "productUpdate failed: Actual precondition is false!"
    _          -> (KrMS5 newWorlds newrel newval, newcur)
