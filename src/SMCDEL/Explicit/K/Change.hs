{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Explicit.K.Change where

import Control.Arrow ((&&&))
import Control.Monad
import Data.List (delete,intercalate)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!),fromList)
import Test.QuickCheck

import SMCDEL.Explicit.K
import SMCDEL.Explicit.S5 (World)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language

type PostCondition = M.Map Prp Form

type Action = Int

data Change = Ch {pre :: Form, post :: PostCondition, rel :: M.Map Agent [Action]}
  deriving (Eq,Ord,Show)

-- | Extend `post` to all propositions
safepost :: Change -> Prp -> Form
safepost ch p | p `elem` M.keys (post ch) = post ch ! p
              | otherwise = PrpF p

newtype ChangeModel = ChM (M.Map Action Change)
  deriving (Eq,Ord,Show)
type PointedChangeModel = (ChangeModel, Action)

type MultipointedChangeModel = (ChangeModel, [Action])

instance HasAgents ChangeModel where
  agentsOf (ChM cm) = M.keys $ rel (head (M.elems cm))

instance HasAgents PointedChangeModel where
  agentsOf = agentsOf . fst

instance HasPrecondition PointedChangeModel where
  preOf (ChM cm, actual) = pre (cm ! actual)

productChangeWithMap :: KripkeModel -> ChangeModel -> (KripkeModel, M.Map (World, Action) World)
productChangeWithMap (KrM m) (ChM cm)
  | agentsOf (KrM m) /= agentsOf (ChM cm) = error "productChange failed: agentsOf differs!"
  | otherwise = (KrM $ fromList (map annotate statePairs), fromList statePairs) where
    statePairs = zip (concat [ [ (s, a) | eval (KrM m, s) (pre $ cm ! a) ] | s <- M.keys m, a <- M.keys cm ]) [0..]
    annotate ((s,a),news) = (news , (newval, fromList (map reachFor (agentsOf (KrM m))))) where
      newval = M.mapWithKey applyPC (fst $ m ! s)
      applyPC p oldbit
        | p `elem` M.keys (post (cm ! a)) = eval (KrM m,s) (post (cm ! a) ! p)
        | otherwise = oldbit
      reachFor i = (i, [ news' | ((s',a'),news') <- statePairs, s' `elem` snd (m !  s) ! i, a' `elem` rel (cm ! a) ! i ])

productChange :: PointedModel -> PointedChangeModel -> PointedModel
productChange (m, cur) (ChM cm, act)
  | not $ eval (m, cur) (pre $ cm ! act) = error "productChange failed: false actual precondition!"
  | otherwise = (newm, newcur) where
      (newm, stateMap) = productChangeWithMap m (ChM cm)
      newcur = stateMap ! (cur,act)

productChangePointless :: KripkeModel -> ChangeModel -> KripkeModel
productChangePointless (KrM m) (ChM cm) = fst $ productChangeWithMap (KrM m) (ChM cm)

productChangeMulti :: PointedModel -> MultipointedChangeModel -> PointedModel
productChangeMulti pm (ChM cm, as) = productChange pm (ChM cm, a) where
  [a] = filter (\x -> eval pm (pre $ cm ! x)) as

publicMakeFalseChM :: [Agent] -> Prp -> PointedChangeModel
publicMakeFalseChM ags p = (ChM $ fromList [ (1::Action, Ch myPre myPost myRel) ], 0) where
  myPre = Top
  myPost = fromList [(p,Bot)]
  myRel = fromList [(i,[1]) | i <- ags]

instance Arbitrary ChangeModel where
  arbitrary = do
    let allactions = [0..3]
    [BF f, BF g, BF h, BF l] <- replicateM 4 (sized $ randomboolformWith [P 0 .. P 4])
    let myPres  = map simplify [f,g,h,l]
    myPosts <- mapM (\_ -> do
      proptochange <- elements [P 0 .. P 4]
      postconcon <- elements $ [Top,Bot] ++ map PrpF [P 0 .. P 4]
      return $ fromList [ (proptochange, postconcon) ]
      ) allactions
    myRels <- mapM (\k -> do
      reachList <- sublistOf allactions
      return $ fromList $ ("0",[k]) : [(show i,reachList) | i <- [1..5::Int]]
      ) allactions
    return $ ChM $ fromList
      [ (k::Action, Ch (myPres !! k) (myPosts !! k) (myRels !! k)) | k <- allactions ]
  shrink (ChM cm) = [ ChM $ removeFromRels k $ M.delete k cm | k <- M.keys cm, k /= 0 ] where
    removeFromRels = M.map . removeFrom where
      removeFrom k c = c { rel = M.map (delete k) (rel c) }

instance KripkeLike ChangeModel where
  directed = const True
  getNodes (ChM cm) = map (show &&& labelOf) (M.keys cm) where
    labelOf a = concat
      [ "$\\begin{array}{c} ? " , tex (pre (cm ! a)) , "\\\\"
      , intercalate "\\\\" (map showPost (M.toList $ post (cm ! a)))
      , "\\end{array}$" ]
    showPost (p,f) = tex p ++ " := " ++ tex f
  getEdges (ChM cm) =
    concat [ [ (i, show a, show b) | b <- rel (cm ! a) ! i ] | a <- M.keys cm, i <- agentsOf (ChM cm) ]
  getActuals = const [ ]

instance TexAble ChangeModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike PointedChangeModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, a) = [show a]

instance TexAble PointedChangeModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot

instance KripkeLike MultipointedChangeModel where
  directed = directed . fst
  getNodes = getNodes . fst
  getEdges = getEdges . fst
  getActuals (_, as) = map show as

instance TexAble MultipointedChangeModel where
  tex = tex.ViaDot
  texTo = texTo.ViaDot
  texDocumentTo = texDocumentTo.ViaDot
