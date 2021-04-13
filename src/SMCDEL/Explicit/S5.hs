{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}

module SMCDEL.Explicit.S5 where

import Control.Arrow (second,(&&&))
import Data.Dynamic
import Data.GraphViz
import Data.List
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)

import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Internal.Help (alleqWith,fusion,apply,(!),lfp)
import Test.QuickCheck

type World = Int

class HasWorlds a where
  worldsOf :: a -> [World]

instance (HasWorlds a, Pointed a b) => HasWorlds (a,b) where worldsOf = worldsOf . fst

type Partition = [[World]]
type Assignment = [(Prp,Bool)]

data KripkeModelS5 = KrMS5 [World] [(Agent,Partition)] [(World,Assignment)] deriving (Eq,Ord,Show)

instance Pointed KripkeModelS5 World
type PointedModelS5 = (KripkeModelS5,World)

instance Pointed KripkeModelS5 [World]
type MultipointedModelS5 = (KripkeModelS5,[World])

instance HasAgents KripkeModelS5 where
  agentsOf (KrMS5 _ rel _) = map fst rel

instance HasVocab KripkeModelS5 where
  vocabOf (KrMS5 _ _ val) = map fst $ snd (head val)

instance HasWorlds KripkeModelS5 where
  worldsOf (KrMS5 ws _ _) = ws

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
    nonActualWorlds <- sublistOf [1..8]
    let worlds = 0 : nonActualWorlds
    val <- mapM (\w -> do
      myAssignment <- zip defaultVocabulary <$> infiniteListOf (choose (True,False))
      return (w,myAssignment)
      ) worlds
    parts <- mapM (\i -> do
      myPartition <- randomPartFor worlds
      return (i,myPartition)
      ) defaultAgents
    return $ KrMS5 worlds parts val
  shrink m@(KrMS5 worlds _ _) =
    [ m `withoutWorld` w | w <- worlds, not (null $ delete w worlds) ]

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
  not (eval pm form1) || eval (update pm form1) form2
eval pm (PubAnnounceW form1 form2) =
  if eval pm form1
    then eval (update pm form1) form2
    else eval (update pm (Neg form1)) form2
eval pm (Announce ags form1 form2) =
  not (eval pm form1) || eval (announce pm ags form1) form2
eval pm (AnnounceW ags form1 form2) =
  if eval pm form1
    then eval (announce pm ags form1) form2
    else eval (announce pm ags (Neg form1)) form2
eval pm (Dia (Dyn dynLabel d) f) = case fromDynamic d of
  Just pactm -> eval pm (preOf (pactm :: PointedActionModelS5)) && eval (pm `update` pactm) f
  Nothing    -> case fromDynamic d of
    Just mpactm -> eval pm (preOf (mpactm :: MultipointedActionModelS5)) && eval (pm `update` mpactm) f
    Nothing     -> error $ "cannot update S5 Kripke model with '" ++ dynLabel ++ "':\n  " ++ show d

valid :: KripkeModelS5 -> Form -> Bool
valid m@(KrMS5 worlds _ _) f = all (\w -> eval (m,w) f) worlds

instance Semantics KripkeModelS5 where
  isTrue m f = all (\w -> isTrue (m,w) f) (worldsOf m)

instance Semantics PointedModelS5 where
  isTrue = eval

instance Semantics MultipointedModelS5 where
  isTrue (m,ws) f = all (\w -> isTrue (m,w) f) ws

instance Update KripkeModelS5 Form where
  unsafeUpdate m@(KrMS5 sts rel val) form = KrMS5 newsts newrel newval where
    newsts = filter (\s -> eval (m,s) form) sts
    newrel = map (second relfil) rel
    relfil = filter ([]/=) . map (filter (`elem` newsts))
    newval = filter (\p -> fst p `elem` newsts) val

instance Update PointedModelS5 Form where
  unsafeUpdate (m,w) f = (unsafeUpdate m f, w)

instance Update MultipointedModelS5 Form where
  unsafeUpdate (m,ws) f =
    let newm = unsafeUpdate m f in (newm, ws `intersect` worldsOf newm)

announce :: PointedModelS5 -> [Agent] -> Form -> PointedModelS5
announce pm@(m@(KrMS5 sts rel val), cur) ags form =
  if eval pm form then (KrMS5 sts newrel val, cur)
                  else error "announce failed: Liar!"
  where
    split ws = map sort.(\(x,y) -> [x,y]) $ partition (\s -> eval (m,s) form) ws
    newrel = map nrel rel
    nrel (i,ri) | i `elem` ags = (i,filter ([]/=) (concatMap split ri))
                | otherwise    = (i,ri)

announceAction :: [Agent] -> [Agent] -> Form -> PointedActionModelS5
announceAction everyone listeners f = (am, 1) where
  am = ActMS5 -- [(Action,(Form,PostCondition))] [(Agent,Partition)]
    [ (1, (f, [])), (2, (Top, [])) ]
    [ (i, if i `elem` listeners then [[1],[2]] else [[1,2]] ) | i <- everyone ]

instance KripkeLike KripkeModelS5 where
  directed = const False
  getNodes (KrMS5 ws _ val) = map (show &&& labelOf) ws where
    labelOf w = tex $ apply val w
  getEdges (KrMS5 _ rel _) =
    nub [ (a,show x,show y) | a <- map fst rel, part <- apply rel a, x <- part, y <- part, x < y ]

instance TexAble KripkeModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, cur) = [show cur]

instance TexAble PointedModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, curs) = map show curs

instance TexAble MultipointedModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

type Bisimulation = [(World,World)]

checkBisim :: Bisimulation -> KripkeModelS5 -> KripkeModelS5 -> Bool
checkBisim [] _                   _                     = False
checkBisim z  m1@(KrMS5 _ rel1 val1) m2@(KrMS5 _ rel2 val2) =
  all (\(w1,w2) ->
        (val1 ! w1 == val2 ! w2)  -- same valuation
    && and [ any (\v2 -> (v1,v2) `elem` z) (concat $ filter (elem w2) (rel2 ! ag)) -- forth
           | ag <- agentsOf m1, v1 <- concat $ filter (elem w1) (rel1 ! ag) ]
    && and [ any (\v1 -> (v1,v2) `elem` z) (concat $ filter (elem w1) (rel1 ! ag)) -- back
           | ag <- agentsOf m2, v2 <- concat $ filter (elem w2) (rel2 ! ag) ]
      ) z

checkBisimPointed :: Bisimulation -> PointedModelS5 -> PointedModelS5 -> Bool
checkBisimPointed z (m1,w1) (m2,w2) = (w1,w2) `elem` z && checkBisim z m1 m2

generatedSubmodel :: PointedModelS5 -> PointedModelS5
generatedSubmodel (KrMS5 oldWorlds rel val, cur) =
  if cur `notElem` oldWorlds
    then error "Actual world is not in the model!"
    else (KrMS5 newWorlds newrel newval, cur) where
      newWorlds :: [World]
      newWorlds = lfp follow [cur] where
        follow xs = sort . nub $ concat [ part | (_,parts) <- rel, part <- parts, any (`elem` part) xs ]
      newrel = map (second $ filter (any (`elem` newWorlds))) rel
      newval = filter (\p -> fst p `elem` newWorlds) val

bisimClasses :: KripkeModelS5 -> [[World]]
bisimClasses m@(KrMS5 _ rel val) = refine sameAssignmentPartition where
  sameAssignmentPartition =
    map (map snd)
      $ groupBy (\x y -> fst x == fst y)
        $ sort (map swap val)
  refine parts = sort $ map sort $ foldl splitByAgent parts (agentsOf m)
  splitByAgent parts a =
    concat [ filter (not . null) [ ws `intersect` aPart | aPart <- rel ! a ] | ws <- parts ]

checkBisimClasses :: KripkeModelS5 -> Bool
checkBisimClasses m =
  and [ checkBisimPointed (swapZ w1 w2) (m,w1) (m,w2)
      | part <- bisimClasses m, w1 <- part, w2 <-part, w1 /= w2 ] where
    swapZ w1 w2 = sort $ [(w1,w2),(w2,w1)] ++ [ (w,w) | w <- worldsOf m \\ [w1,w2] ]

bisiminimize :: PointedModelS5 -> PointedModelS5
bisiminimize (m,w) =
  if all ((==1) . length) (bisimClasses m)
    then (m,w) -- nothing to minimize
    else (KrMS5 newWorlds newRel newVal, copyFct w) where
      KrMS5 _ oldRel oldVal = m
      copyRel      = zip (bisimClasses m) [1..]
      copyFct wOld = snd $ head $ filter ((wOld `elem`) . fst) copyRel
      newWorlds    = map snd copyRel
      newRel       = [ (a,newRelFor a) | a <- agentsOf m ]
      newRelFor a  = [ nub [ copyFct wOld | wOld <- part ] |  part <- oldRel ! a ]
      newVal       = [ (wNew, oldVal ! wOld) | (wOld:_,wNew) <- copyRel ]

instance Optimizable PointedModelS5 where
  optimize _ = bisiminimize . generatedSubmodel

type Action = Int
type PostCondition = [(Prp,Form)]

data ActionModelS5 = ActMS5 [(Action,(Form,PostCondition))] [(Agent,Partition)]
  deriving (Eq,Ord,Show)

instance HasAgents ActionModelS5 where
  agentsOf (ActMS5 _ rel) = map fst rel

-- | A safe way to `lookup` all postconditions
safepost :: PostCondition -> Prp -> Form
safepost posts p = fromMaybe (PrpF p) (lookup p posts)

instance Pointed ActionModelS5 Action
type PointedActionModelS5 = (ActionModelS5, Action)

instance HasPrecondition ActionModelS5 where
  preOf _ = Top

instance HasPrecondition PointedActionModelS5 where
  preOf (ActMS5 acts _, actual) = fst (acts ! actual)

instance Pointed ActionModelS5 [Action]
type MultipointedActionModelS5 = (ActionModelS5,[Action])

instance HasPrecondition MultipointedActionModelS5 where
  preOf (am, actuals) = Disj [ preOf (am, a) | a <- actuals ]

instance KripkeLike ActionModelS5 where
  directed = const False
  getNodes (ActMS5 acts _) = map labelOf acts where
    labelOf (a,(pre,posts)) = (show a, concat
      [ "$\\begin{array}{c} ? " , tex pre, "\\\\"
      , intercalate "\\\\" (map showPost posts)
      , "\\end{array}$" ])
    showPost (p,f) = tex p ++ " := " ++ tex f
  getEdges am@(ActMS5 _ rel) =
    nub [ (a, show x, show y) | a <- agentsOf am, part <- rel ! a, x <- part, y <- part, x < y ]
  getActuals _ = [ ]
  nodeAts _ True  = [shape BoxShape, style solid]
  nodeAts _ False = [shape BoxShape, style dashed]

instance TexAble ActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedActionModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, cur) = [show cur]

instance TexAble PointedActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedActionModelS5 where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, curs) = map show curs

instance TexAble MultipointedActionModelS5 where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance Arbitrary ActionModelS5 where
  arbitrary = do
    BF f <- sized $ randomboolformWith [P 0 .. P 4]
    BF g <- sized $ randomboolformWith [P 0 .. P 4]
    BF h <- sized $ randomboolformWith [P 0 .. P 4]
    myPost <- (\_ -> do
      proptochange <- elements [P 0 .. P 4]
      postconcon <- elements $ [Top,Bot] ++ map PrpF [P 0 .. P 4]
      return [ (proptochange, postconcon) ]
      ) (0::Action)
    return $
      ActMS5
        [ (0,(Top,[]))
        , (1,(f  ,[]))
        , (2,(g  ,myPost))
        , (3,(h  ,[]))     ]
        ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3::Int]]) | k<-[1..5::Int] ])

instance Update KripkeModelS5 ActionModelS5 where
  checks = [haveSameAgents]
  unsafeUpdate m am@(ActMS5 acts _) =
    let (newModel,_) = unsafeUpdate (m, worldsOf m) (am, map fst acts) in newModel

instance Update PointedModelS5 PointedActionModelS5 where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) (actm, a) =
    let (newModel,[newWorld]) = unsafeUpdate (m, [w]) (actm, [a]) in (newModel,newWorld)

instance Update PointedModelS5 MultipointedActionModelS5 where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) mpactm =
    let (newModel,[newWorld]) = unsafeUpdate (m, [w]) mpactm in (newModel,newWorld)

instance Update MultipointedModelS5 PointedActionModelS5 where
  checks = [haveSameAgents] -- do not check precondition!
  unsafeUpdate mpm (actm, a) = unsafeUpdate mpm (actm, [a])

instance Update MultipointedModelS5 MultipointedActionModelS5 where
  checks = [haveSameAgents] -- do not check precondition!
  unsafeUpdate (m@(KrMS5 oldWorlds oldrel oldval), oldcurs) (ActMS5 acts actrel, factions) =
    (KrMS5 newWorlds newrel newval, newcurs) where
      startcount        = maximum oldWorlds + 1
      copiesOf (s,a)    = [ (s, a, a * startcount + s) | eval (m, s) (fst $ acts ! a) ]
      newWorldsTriples  = concat [ copiesOf (s,a) | s <- oldWorlds, (a,_) <- acts ]
      newWorlds         = map (\(_,_,x) -> x) newWorldsTriples
      newval            = map (\(s,a,t) -> (t, newValAt (s,a))) newWorldsTriples where
        newValAt sa = [ (p, newValAtFor sa p) | p <- vocabOf m ]
        newValAtFor (s,a) p = case lookup p (snd (acts ! a)) of
          Just postOfP -> eval (m, s) postOfP
          Nothing      -> (oldval ! s) ! p
      listFor ag        = cartProd (apply oldrel ag) (apply actrel ag)
      newPartsFor ag    = [ cartProd as bs | (as,bs) <- listFor ag ]
      translSingle pair = filter (`elem` newWorlds) $ map (\(_,_,x) -> x) $ copiesOf pair
      transEqClass      = concatMap translSingle
      nTransPartsFor ag = filter (/= []) $ map transEqClass (newPartsFor ag)
      newrel            = [ (a, nTransPartsFor a)  | a <- map fst oldrel ]
      newcurs           = concat [ map (\(_,_,x) -> x) $ copiesOf (s,a) | s <- oldcurs, a <- factions ]
      cartProd xs ys    = [ (x,y) | x <- xs, y <- ys ]
