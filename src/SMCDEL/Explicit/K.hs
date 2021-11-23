{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SMCDEL.Explicit.K where

import Control.Arrow ((&&&),second)
import Data.Containers.ListUtils (nubInt,nubOrd)
import Data.Dynamic
import Data.List (sort,(\\),delete,intercalate,intersect)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Data.Maybe (isJust,isNothing)
import Test.QuickCheck

import SMCDEL.Language
import SMCDEL.Explicit.S5 (Action,Bisimulation,HasWorlds,World,worldsOf)
import SMCDEL.Internal.Help (alleqWith,lfp)
import SMCDEL.Internal.TexDisplay

newtype KripkeModel = KrM (M.Map World (M.Map Prp Bool, M.Map Agent [World]))
  deriving (Eq,Ord,Show)

instance Pointed KripkeModel World
type PointedModel = (KripkeModel, World)

instance Pointed KripkeModel [World]
type MultipointedModel = (KripkeModel,[World])

distinctVal :: KripkeModel -> Bool
distinctVal (KrM m) = M.size m == length (nubOrd (map fst (M.elems m)))

instance HasWorlds KripkeModel where
  worldsOf (KrM m) = M.keys m

instance HasVocab KripkeModel where
  vocabOf (KrM m) = M.keys $ fst (head (M.elems m))

instance HasAgents KripkeModel where
  agentsOf (KrM m) = M.keys $ snd (head (M.elems m))

relOfIn :: Agent -> KripkeModel -> M.Map World [World]
relOfIn i (KrM m) = M.map (\x -> snd x ! i) m

truthsInAt :: KripkeModel -> World -> [Prp]
truthsInAt (KrM m) w = M.keys (M.filter id (fst (m ! w)))

instance KripkeLike KripkeModel where
  directed = const True
  getNodes m = map (show . fromEnum &&& labelOf) (worldsOf m) where
    labelOf w = "$" ++ tex (truthsInAt m w) ++ "$"
  getEdges m =
    concat [ [ (a, show $ fromEnum w, show $ fromEnum v) | v <- relOfIn a m ! w ] | w <- worldsOf m, a <- agentsOf m ]
  getActuals = const []

instance KripkeLike PointedModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals = return . show . fromEnum . snd

instance KripkeLike MultipointedModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals = map (show . fromEnum) . snd

instance TexAble KripkeModel       where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance TexAble PointedModel      where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance TexAble MultipointedModel where
  tex           = tex.ViaDot
  texTo         = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance Arbitrary KripkeModel where
  arbitrary = do
    nonActualWorlds <- sublistOf [1..8]
    let worlds = 0 : nonActualWorlds
    m <- mapM (\w -> do
      myAssignment <- zip defaultVocabulary <$> infiniteListOf (choose (True,False))
      myRelations <- mapM (\a -> do
        reachables <- sublistOf worlds
        return (a,reachables)
        ) defaultAgents
      return (w, (M.fromList myAssignment, M.fromList myRelations)) -- FIXME avoid fromList, build M.map directly?
      ) worlds
    return $ KrM $ M.fromList m
  shrink krm = [ krm `withoutWorld` w | length (worldsOf krm) > 1, w <- delete 0 (worldsOf krm) ]

withoutWorld :: KripkeModel -> World -> KripkeModel
withoutWorld (KrM m) w = KrM $ M.map (second (M.map (delete w))) $ M.delete w m

eval :: PointedModel -> Form -> Bool
eval _     Top           = True
eval _     Bot           = False
eval (m,w) (PrpF p)      = p `elem` truthsInAt m w
eval pm    (Neg f)       = not $ eval pm f
eval pm    (Conj fs)     = all (eval pm) fs
eval pm    (Disj fs)     = any (eval pm) fs
eval pm    (Xor  fs)     = odd $ length (filter id $ map (eval pm) fs)
eval pm    (Impl f g)    = not (eval pm f) || eval pm g
eval pm    (Equi f g)    = eval pm f == eval pm g
eval pm    (Forall ps f) = eval pm (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
eval pm    (Exists ps f) = eval pm (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
eval (KrM m,w) (K   i f) = all (\w' -> eval (KrM m,w') f) (snd (m ! w) ! i)
eval (KrM m,w) (Kw  i f) = alleqWith (\w' -> eval (KrM m,w') f) (snd (m ! w) ! i)
eval (m,w) (Ck ags form) = all (\w' -> eval (m,w') form) (groupRel m ags w)
eval (m,w) (Ckw ags form) = alleqWith (\w' -> eval (m,w') form) (groupRel m ags w)
eval (m,w) (PubAnnounce f g) = not (eval (m,w) f) || eval (update (m,w) f) g
eval (m,w) (PubAnnounceW f g) = eval (update m aform, w) g where
  aform | eval (m,w) f = f
        | otherwise     = Neg f
eval (m,w) (Announce listeners f g) = not (eval (m,w) f) || eval newm g where
  newm = (m,w) `update` announceAction (agentsOf m) listeners f
eval (m,w) (AnnounceW listeners f g) = eval newm g where
  newm = (m,w) `update` announceAction (agentsOf m) listeners aform
  aform | eval (m,w) f = f
        | otherwise    = Neg f
eval pm (Dia (Dyn dynLabel d) f) = case fromDynamic d of
  Just pactm -> eval pm (preOf (pactm :: PointedActionModel)) && eval (pm `update` pactm) f
  Nothing    -> error $ "cannot update Kripke model with '" ++ dynLabel ++ "':\n  " ++ show d

instance Semantics PointedModel where
  isTrue = eval

instance Semantics KripkeModel where
  isTrue m = isTrue (m, worldsOf m)

instance Semantics MultipointedModel where
  isTrue (m,ws) f = all (\w -> isTrue (m,w) f) ws

groupRel :: KripkeModel -> [Agent] -> World -> [World]
groupRel (KrM m) ags w = sort $ lfp extend (oneStepReachFrom w) where
  oneStepReachFrom x = concat [ snd (m ! x) ! a | a <- ags ]
  extend xs = nubInt $ xs ++ concatMap oneStepReachFrom xs

instance Update KripkeModel Form where
  checks = [ ] -- unpointed models can always be updated with any formula
  unsafeUpdate (KrM m) f = KrM newm where
    newm = M.mapMaybeWithKey isin m
    isin w' (v,rs) | eval (KrM m,w') f = Just (v, M.map newr rs)
                   | otherwise         = Nothing
    newr = filter (`elem` M.keys newm)

instance Update PointedModel Form where
  unsafeUpdate (m,w) f = (unsafeUpdate m f, w)

instance Update MultipointedModel Form where
  unsafeUpdate (m,ws) f =
    let newm = unsafeUpdate m f in (newm, ws `intersect` worldsOf newm)

announceAction :: [Agent] -> [Agent] -> Form -> PointedActionModel
announceAction everyone listeners f = (ActM am, 1) where
  am = M.fromList
    [ (1, Act { pre = f,   post = M.empty, rel = M.fromList $ [(i,[1]) | i <- listeners] ++ [(i,[2]) | i <- everyone \\ listeners] } )
    , (2, Act { pre = Top, post = M.empty, rel = M.fromList [(i,[2]) | i <- everyone] } )
    ]

checkBisim :: Bisimulation -> KripkeModel -> KripkeModel -> Bool
checkBisim [] _  _  = False
checkBisim z  m1 m2 =
  all (\(w1,w2) ->
        (truthsInAt m1 w1 == truthsInAt m2 w2)  -- same valuation
    && and [ any (\v2 -> (v1,v2) `elem` z) (relOfIn ag m2 ! w2) -- forth
           | ag <- agentsOf m1, v1 <- relOfIn ag m1 ! w1 ]
    && and [ any (\v1 -> (v1,v2) `elem` z) (relOfIn ag m1 ! w1) -- back
           | ag <- agentsOf m2, v2 <- relOfIn ag m2 ! w2 ]
      ) z

checkBisimPointed :: Bisimulation -> PointedModel -> PointedModel -> Bool
checkBisimPointed z (m1,w1) (m2,w2) = (w1,w2) `elem` z && checkBisim z m1 m2

type Status = Maybe Form
type StatusMap = M.Map (World,World) Status

diff :: KripkeModel -> KripkeModel -> StatusMap
diff m1 m2 = lfp step start where
  -- initialize using differences in atomic propositions given by valuation
  start = M.fromList [ ((w1,w2), propDiff (truthsInAt m1 w1) (truthsInAt m2 w2))
                     |  w1 <- worldsOf m1, w2 <- worldsOf m2 ]
  propDiff ps qs | ps \\ qs /= []  = Just $       PrpF $ head (ps \\ qs)
                 | qs \\ ps /= []  = Just $ Neg $ PrpF $ head (qs \\ ps)
                 | otherwise       = Nothing
  -- until a fixpoint is reached, update the map using all relations
  step curMap = M.mapWithKey (updateAt curMap) curMap
  updateAt _      _       (Just f) = Just f
  updateAt curMap (w1,w2) Nothing  = case
    -- forth
    [ Neg . K i . Neg . Conj $ [ f | w2' <- w2's, let Just f = curMap ! (w1',w2') ]
    | i <- agentsOf m1
    , let w2's = relOfIn i m2 ! w2
    , w1' <- relOfIn i m1 ! w1
    , all (\w2' -> isJust $ curMap ! (w1',w2')) w2's
    ]
    ++
    -- back
    [ K i . Disj $ [ f | w1' <- w1's, let Just f = curMap ! (w1',w2') ]
    | i <- agentsOf m1
    , let w1's = relOfIn i m1 ! w1
    , w2' <- relOfIn i m2 ! w2
    , all (\w1' -> isJust $ curMap ! (w1',w2')) w1's
    ]
    of
      [] -> Nothing
      (f:_) -> Just f

diffPointed :: PointedModel -> PointedModel -> Either Bisimulation Form
diffPointed (m1,w1) (m2,w2) =
  case diff m1 m2 ! (w1,w2) of
    Nothing -> Left $ M.keys $ M.filter isNothing (diff m1 m2)
    Just f -> Right f

generatedSubmodel :: PointedModel -> PointedModel
generatedSubmodel (KrM m, cur) = (KrM newm, cur) where
  newm = M.mapMaybeWithKey isin m
  isin w' (v,rs) | w' `elem` reachable = Just (v, M.map newr rs)
                 | otherwise           = Nothing
  newr = filter (`elem` M.keys newm)
  reachable = lfp follow [cur] where
    follow xs = sort . nubInt $ concat [ snd (m ! x) ! a | x <- xs, a <- agentsOf (KrM m) ]

type PostCondition = M.Map Prp Form

data Act = Act {pre :: Form, post :: PostCondition, rel :: M.Map Agent [Action]}
  deriving (Eq,Ord,Show)

-- | Extend `post` to all propositions
safepost :: Act -> Prp -> Form
safepost ch p | p `elem` M.keys (post ch) = post ch ! p
              | otherwise = PrpF p

newtype ActionModel = ActM (M.Map Action Act)
  deriving (Eq,Ord,Show)

instance HasAgents ActionModel where
  agentsOf (ActM am) = M.keys $ rel (head (M.elems am))

instance HasPrecondition ActionModel where
  preOf _ = Top

instance Pointed ActionModel Action
type PointedActionModel = (ActionModel, Action)

instance HasPrecondition PointedActionModel where
  preOf (ActM am, actual) = pre (am ! actual)

instance Pointed ActionModel [Action]
type MultipointedActionModel = (ActionModel, [Action])

instance HasPrecondition MultipointedActionModel where
  preOf (ActM am, as) = Disj [ pre (am ! a) | a <- as ]

instance Update KripkeModel ActionModel where
  checks = [haveSameAgents]
  unsafeUpdate m (ActM am) =
    let (newModel,_) = unsafeUpdate (m, worldsOf m) (ActM am, M.keys am) in newModel

instance Update PointedModel PointedActionModel where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) (actm, a) =
    let (newModel,[newWorld]) = unsafeUpdate (m, [w]) (actm, [a]) in (newModel,newWorld)

instance Update PointedModel MultipointedActionModel where
  checks = [haveSameAgents,preCheck]
  unsafeUpdate (m, w) mpactm =
    let (newModel,[newWorld]) = unsafeUpdate (m, [w]) mpactm in (newModel,newWorld)

instance Update MultipointedModel PointedActionModel where
  checks = [haveSameAgents] -- do not check precondition!
  unsafeUpdate mpm (actm, a) = unsafeUpdate mpm (actm, [a])

instance Update MultipointedModel MultipointedActionModel where
  checks = [haveSameAgents]
  unsafeUpdate (KrM m, ws) (ActM am, facts) =
    (KrM $ M.fromList (map annotate worldPairs), newActualWorlds) where
      worldPairs = zip (concat [ [ (s, a) | eval (KrM m, s) (pre $ am ! a) ] | s <- M.keys m, a <- M.keys am ]) [0..]
      newActualWorlds = [ k | ((w,a),k) <- worldPairs, w `elem` ws, a `elem` facts ]
      annotate ((s,a),news) = (news , (newval, M.fromList (map reachFor (agentsOf (KrM m))))) where
        newval = M.mapWithKey applyPC (fst $ m ! s)
        applyPC p oldbit
          | p `elem` M.keys (post (am ! a)) = eval (KrM m,s) (post (am ! a) ! p)
          | otherwise = oldbit
        reachFor i = (i, [ news' | ((s',a'),news') <- worldPairs, s' `elem` snd (m !  s) ! i, a' `elem` rel (am ! a) ! i ])

instance Arbitrary ActionModel where
  arbitrary = do
    let allactions = [0..3]
    BF f <- sized $ randomboolformWith defaultVocabulary
    BF g <- sized $ randomboolformWith defaultVocabulary
    BF h <- sized $ randomboolformWith defaultVocabulary
    let myPres  = Top : map simplify [f,g,h]
    myPosts <- mapM (\_ -> do
      proptochange <- elements defaultVocabulary
      postconcon <- elements $ [Top,Bot] ++ map PrpF defaultVocabulary
      return $ M.fromList [ (proptochange, postconcon) ]
      ) allactions
    myRels <- mapM (\k -> do
      reachList <- sublistOf allactions
      return $ M.fromList $ ("1",[k]) : [ (ag,reachList) | ag <- tail defaultAgents ]
      ) allactions
    return $ ActM $ M.fromList
      [ (k::Action, Act (myPres !! k) (myPosts !! k) (myRels !! k)) | k <- allactions ]
  shrink (ActM am) = [ ActM $ removeFromRels k $ M.delete k am | k <- M.keys am, k /= 0 ] where
    removeFromRels = M.map . removeFrom where
      removeFrom k c = c { rel = M.map (delete k) (rel c) }

instance KripkeLike ActionModel where
  directed = const True
  getNodes (ActM am) = map (show &&& labelOf) (M.keys am) where
    labelOf a = concat
      [ "$\\begin{array}{c} ? " , tex (pre (am ! a)) , "\\\\"
      , intercalate "\\\\" (map showPost (M.toList $ post (am ! a)))
      , "\\end{array}$" ]
    showPost (p,f) = tex p ++ " := " ++ tex f
  getEdges (ActM am) =
    concat [ [ (i, show a, show b) | b <- rel (am ! a) ! i ] | a <- M.keys am, i <- agentsOf (ActM am) ]
  getActuals = const [ ]

instance TexAble ActionModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedActionModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, a) = [show a]

instance TexAble PointedActionModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedActionModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, as) = map show as

instance TexAble MultipointedActionModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot
