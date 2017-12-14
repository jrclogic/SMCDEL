
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Other.Change where

import Control.Arrow ((&&&))
import Control.Lens (over,both)
import Control.Monad
import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),delete,intersect,intercalate,nub,sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!),fromList,toList)
import Test.QuickCheck

import SMCDEL.Explicit.Simple (World)
import SMCDEL.Internal.Help (apply,powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Translations (booloutof)
import SMCDEL.Other.BDD2Form
import SMCDEL.Other.NonS5
import SMCDEL.Symbolic.HasCacBDD (bddEval,boolBddOf)

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

productChangeWithMap :: GeneralKripkeModel -> ChangeModel -> (GeneralKripkeModel, M.Map (World, Action) World)
productChangeWithMap (GKM m) (ChM cm)
  | agentsOf (GKM m) /= agentsOf (ChM cm) = error "productChange failed: agentsOf differs!"
  | otherwise = (GKM $ fromList (map annotate statePairs), fromList statePairs) where
    statePairs = zip (concat [ [ (s, a) | eval (GKM m, s) (pre $ cm ! a) ] | s <- M.keys m, a <- M.keys cm ]) [0..]
    annotate ((s,a),news) = (news , (newval, fromList (map reachFor (agentsOf (GKM m))))) where
      newval = M.mapWithKey applyPC (fst $ m ! s)
      applyPC p oldbit
        | p `elem` M.keys (post (cm ! a)) = eval (GKM m,s) (post (cm ! a) ! p)
        | otherwise = oldbit
      reachFor i = (i, [ news' | ((s',a'),news') <- statePairs, s' `elem` snd (m !  s) ! i, a' `elem` rel (cm ! a) ! i ])

productChange :: GeneralPointedModel -> PointedChangeModel -> GeneralPointedModel
productChange (m, cur) (ChM cm, act)
  | not $ eval (m, cur) (pre $ cm ! act) = error "productChange failed: false actual precondition!"
  | otherwise = (newm, newcur) where
      (newm, stateMap) = productChangeWithMap m (ChM cm)
      newcur = stateMap ! (cur,act)

productChangePointless :: GeneralKripkeModel -> ChangeModel -> GeneralKripkeModel
productChangePointless (GKM m) (ChM cm) = fst $ productChangeWithMap (GKM m) (ChM cm)

productChangeMulti :: GeneralPointedModel -> MultipointedChangeModel -> GeneralPointedModel
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
    [BF f, BF g, BF h] <- replicateM 3 (sized $ randomboolformWith [P 0 .. P 4])
    let myPres  = map simplify [Top,f,g,h]
    myPosts <- mapM (\_ -> do
      cons <- elements [Top,Bot]
      return $ fromList [ (P 1, cons) ]
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

    -- ActM [0..3] [(0,Top),(1,f),(2,g),(3,h)] ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3::Int]]) | k<-[1..5::Int] ])

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

type State = [Prp]

data Transformer = Trf
  [Prp] -- addprops
  Form  -- addlaw
  [Prp] -- changeprops
  (M.Map Prp Bdd) -- changelaw
  (M.Map Agent RelBDD) -- eventObs
  deriving (Eq,Show)

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ _ obdds) = M.keys obdds

type Event = (Transformer,State)

type MultiEvent = (Transformer,[State])
-- TODO: make it symbolic with a BDD instead of [State]

instance TexAble Transformer where
  tex (Trf addprops addlaw changeprops changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", "
    , tex addlaw, ", "
    , tex changeprops, ", "
    , intercalate ", " $ map snd . toList $ M.mapWithKey texChange changelaw, ", "
    , intercalate ", " eobddstrings
    , " \\right) \n"
    ] where
        texChange prop changebdd = tex prop ++ " := " ++ tex (formOf changebdd)
        eobddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (toList eventObs)
        bddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", ", tex eventFacts, " \\right) \n" ]

-- TODO: this is horribly long, shifting should be done separately before!
transform :: GenScenario -> Event -> GenScenario
transform (kns@(GenKnS props lawbdd obdds),s) (Trf addprops addlaw changeprops changelaw eventObs, eventFacts) =
  (GenKnS newprops newlawbdd newobs, news) where
    -- shift addprops to ensure props and newprops are disjoint:
    shiftaddprops = [(freshp props)..]
    shiftrel = sort $ zip addprops shiftaddprops
    shiftrelVars = sort $ map (over both fromEnum) shiftrel
    -- copies of modified propositions:
    copychangeprops = [(freshp $ props ++ map snd shiftrel)..]
    copyrel = zip changeprops copychangeprops
    copyrelVars = sort $ map (over both fromEnum) copyrel
    -- new vocabulary:
    newprops = sort $ props ++ map snd shiftrel ++ map snd copyrel
    -- new law:
    newlawbdd = con
      (relabel copyrelVars (con lawbdd (bddOf kns (replPsInF shiftrel addlaw))))
      (conSet [var (fromEnum q) `equ` relabel copyrelVars (relabel shiftrelVars $ changelaw ! q) | q <- changeprops])
    -- copies of modified propositions in double vocabulary:
    copyrelMV = zip (mv changeprops) (mv copychangeprops)
    copyrelCP = zip (cp changeprops) (cp copychangeprops)
    -- check disjointness before combining MV and CP relations:
    copyrelMVCPVars = if null $ (map fst copyrelMV `intersect` map fst copyrelCP)
                             ++ (map snd copyrelMV `intersect` map snd copyrelCP)
      then sort $ map (over both fromEnum) (copyrelMV ++ copyrelCP)
      else error "copyrelMV and copyrelCP are not disjoint!"
    copyrelMVCP = relabel copyrelMVCPVars -- modified copy substitution for BDDs
    -- shifted added propositions in double vocabulary:
    shiftrelMV = zip (mv addprops) (mv shiftaddprops)
    shiftrelCP = zip (cp addprops) (cp shiftaddprops)
    -- again, check for disjointness before combining MV and CP:
    shiftrelMVCPVars = if null $ copyrelMV `intersect` copyrelCP
      then sort $ map (over both fromEnum) (shiftrelMV ++ shiftrelCP)
      else error "shiftrelMV and shiftrelCP are not disjoint!"
    shiftrelMVCP = relabel shiftrelMVCPVars -- shifted add substitution for BDDs
    -- new observations: combine modified oldobs with shifted eventObs
    newobs = M.mapWithKey
      (\i oldobs -> con <$> (copyrelMVCP <$> oldobs) <*> (shiftrelMVCP <$> (eventObs ! i))) obdds
    -- new state:
    x = map (apply shiftrel) eventFacts
    news =
      if not $ bddEval (sort $ s ++ x) (con lawbdd (bddOf kns (replPsInF shiftrel addlaw)))
        then error "Transformer is not applicable!"
        else sort $ concat
      [ s \\ changeprops -- unchanged old props
      , map (apply copyrel) $ s `intersect` changeprops -- copies of modified props
      , x -- the actual event
      , filter (\ p -> bddEval (sort $ s ++ x) (relabel shiftrelVars $ changelaw ! p)) changeprops -- changed props now true
      ]

transformMulti :: GenScenario -> MultiEvent -> GenScenario
transformMulti (kns,s) (trf@(Trf addprops addlaw _ _ _), eventsFacts) =
  transform (kns,s) (trf,selectedEventFacts) where
    possible :: State -> Bool
    possible eventFact = evalViaBdd (kns,s) (substitSet subs addlaw) where
      subs = [ (p, if p `elem` eventFact then Top else Bot) |  p <- addprops ]
    selectedEventFacts :: State
    [selectedEventFacts] = filter possible eventsFacts

publicMakeFalse :: [Agent] -> Prp -> Event
publicMakeFalse agents p = (Trf [] Top [p] mychangelaw myobs, []) where
  mychangelaw = fromList [ (p,boolBddOf Bot) ]
  myobs = fromList [ (i,totalRelBdd) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalse (agentsOf $ fst SMCDEL.Other.NonS5.exampleStart) (P 0)

tResult :: GenScenario
tResult = SMCDEL.Other.NonS5.exampleStart `transform` myEvent

flipOverAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipOverAndShowTo everyone p i = (Trf [q] eventlaw [p] changelaw obs, [q]) where
  q = freshp [p]
  eventlaw = PrpF q `Equi` PrpF p
  changelaw = fromList [ (p, boolBddOf . Neg . PrpF $ p) ]
  obs = fromList $
    (i, allsamebdd  [q]) :
    [ (j,totalRelBdd) | j <- everyone \\ [i] ]

myOtherEvent :: Event
myOtherEvent = flipOverAndShowTo ["1","2"] (P 0) "1"

tResult2 :: GenScenario
tResult2 = SMCDEL.Other.NonS5.exampleStart `transform` myOtherEvent

actionToEvent :: PointedChangeModel -> Event
actionToEvent (ChM chm, faction) = (Trf addprops addlaw changeprops changelaw eventObs, efacts) where
  actions      = M.keys chm
  (P fstnewp)  = freshp $ concatMap -- avoid props in pre and postconditions
    (\c -> propsInForms (pre c : M.elems (post c)) ++ M.keys (post c)) (M.elems chm)
  addprops     = [P fstnewp..P maxactprop] -- new props to distinguish all actions
  maxactprop   = fstnewp + ceiling (logBase 2 (fromIntegral $ length actions) :: Float) - 1
  ell          = apply $ zip actions (powerset addprops) -- injectively label actions with sets of propositions
  addlaw       = simplify $ Disj [ Conj [ booloutofForm (ell a) addprops, pre $ chm ! a ] | a <- actions ]
  changeprops  = sort $ nub $ concatMap M.keys . M.elems $ M.map post chm -- propositions to be changed
  changelaw    = M.fromList [ (p, changeFor p) | p <- changeprops ] -- encode postconditions
  changeFor p  = disSet [ booloutof (ell k) addprops `con` boolBddOf (safepost (chm ! k) p) | k <- actions ]
  eventObs     = M.fromList [ (i, obsLawFor i) | i <- agentsOf (ChM chm) ]
  obsLawFor i  = pure $ disSet (M.elems $ M.mapWithKey (link i) chm)
  link i k ch  = booloutof (mv $ ell k) (mv addprops) `con` -- encode relations
                 disSet [ booloutof (cp $ ell there) (cp addprops) | there <- rel ch ! i ]
  efacts       = ell faction

eventToAction' :: Event -> PointedChangeModel
eventToAction' (t@(Trf addprops addlaw changeprops changelaw eventObs), efacts) = (ChM chm, faction) where
  actlist    = zip (powerset addprops) [0..]
  chm        = fromList [ (a, Ch (preFor ps) (postFor ps) (relFor ps)) | (ps,a) <- actlist ]
  preFor ps  = simplify $
    substitSet (zip ps (repeat Top) ++ zip (addprops \\ ps) (repeat Bot)) addlaw
  postFor ps = fromList
    [ (q, formOf $ restrictSet (changelaw ! q) [(p, P p `elem` ps) | (P p) <- addprops]) | q <- changeprops ]
  relFor ps = fromList [(i,rFor i) | i <- agentsOf t] where
    rFor i = concatMap (\(qs,b) -> [ b | tagBddEval (mv ps ++ cp qs) (eventObs ! i) ]) actlist
  faction   = apply actlist efacts

-- TODO eventToAction :: Event -> PointedChangeModel
-- Can we use M.filter to remove the actions with \bot precondition?

coinStart :: GenScenario
coinStart = (GenKnS [P 0] law obs, actual) where
  law    = boolBddOf (PrpF $ P 0)
  obs    = fromList [ ("a", allsamebdd [P 0]), ("b", allsamebdd [P 0]) ]
  actual = [P 0]

flipRandomAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipRandomAndShowTo everyone p i = (Trf [q] eventlaw [p] changelaw obs, [q]) where
  q = freshp [p]
  eventlaw = Top
  changelaw = fromList [ (p, boolBddOf $ PrpF q) ]
  obs = fromList $
    (i, allsamebdd  [q]) :
    [ (j,totalRelBdd) | j <- everyone \\ [i] ]

coinFlip :: Event
coinFlip = flipRandomAndShowTo ["a","b"] (P 0) "b"

coinResult :: GenScenario
coinResult = coinStart `transform` coinFlip

pp, qq, tt :: Prp
pp = P 0
tt = P 1
qq = P 7 -- this number should not matter!

sallyInit :: GenScenario
sallyInit = (GenKnS [pp, tt] law obs, actual) where
  law    = boolBddOf $ Conj [PrpF pp, Neg (PrpF tt)]
  obs    = fromList [ ("Sally", totalRelBdd), ("Anne", totalRelBdd) ]
  actual = [pp]

sallyPutsMarbleInBasket :: Event
sallyPutsMarbleInBasket = (Trf [] Top [tt]
  (fromList [ (tt,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate1 :: GenScenario
sallyIntermediate1 = sallyInit `transform` sallyPutsMarbleInBasket

sallyLeaves :: Event
sallyLeaves = (Trf [] Top [pp]
  (fromList [ (pp,boolBddOf Bot) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate2 :: GenScenario
sallyIntermediate2 = sallyIntermediate1 `transform` sallyLeaves

annePutsMarbleInBox :: Event
annePutsMarbleInBox = (Trf [qq] Top [tt]
  (fromList [ (tt,boolBddOf $ Conj [Neg (PrpF qq) `Impl` PrpF tt, PrpF qq `Impl` Bot]) ])
  (fromList [ ("Anne", allsamebdd [qq]), ("Sally", cpBdd $ boolBddOf $ Neg (PrpF qq))  ]), [qq])

sallyIntermediate3 :: GenScenario
sallyIntermediate3 = sallyIntermediate2 `transform` annePutsMarbleInBox

sallyComesBack :: Event
sallyComesBack = (Trf [] Top [pp]
  (fromList [ (pp,boolBddOf Top) ])
  (fromList [ (i,totalRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate4 :: GenScenario
sallyIntermediate4 = sallyIntermediate3 `transform` sallyComesBack

sallyFinal :: GenScenario
sallyFinal = sallyInit
              `transform` sallyPutsMarbleInBasket
              `transform` sallyLeaves
              `transform` annePutsMarbleInBox
              `transform` sallyComesBack

sallyFinalCheck :: (Bool,Bool)
sallyFinalCheck =
  ( SMCDEL.Other.NonS5.evalViaBdd sallyFinal (K "Sally" (PrpF tt))
  , sallyIntermediate4 == sallyFinal )
