
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Other.Change where

import Control.Arrow ((&&&))
import Control.Lens (over,both)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),intersect,intercalate,sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!),fromList,toList)
import Data.Maybe (fromJust)
import SMCDEL.Other.BDD2Form

import SMCDEL.Internal.Help (apply)
import SMCDEL.Language
import SMCDEL.Other.NonS5
import SMCDEL.Symbolic.HasCacBDD (bddEval,boolBddOf)
import SMCDEL.Internal.TexDisplay

type PostCondition = M.Map Prp Form

type Action = Int

data Change = Ch {pre :: Form, post :: PostCondition, rel :: M.Map Agent [Action]}
  deriving (Eq,Ord,Show)

newtype ChangeModel = ChM (M.Map Action Change)
  deriving (Eq,Ord,Show)
type PointedChangeModel = (ChangeModel, Action)

instance HasAgents ChangeModel where
  agentsOf (ChM cm) = M.keys $ rel (head (M.elems cm))

instance HasAgents PointedChangeModel where
  agentsOf = agentsOf . fst

productChange :: GeneralPointedModel -> PointedChangeModel -> GeneralPointedModel
productChange (GKM m, oldcur) (ChM cm, act)
  | agentsOf (GKM m) /= agentsOf (ChM cm)       = error "productChange failed: Agents of GKM and ChM are not the same!"
  | not $ eval (GKM m, oldcur) (pre $ cm ! act) = error "productChange failed: Actual precondition is false!"
  | otherwise = (GKM $ fromList (map annotate statePairs), newcur) where
    statePairs = zip (concat [ [ (s, a) | eval (GKM m, s) (pre $ cm ! a) ] | s <- M.keys m, a <- M.keys cm ]) [0..]
    annotate ((s,a),news) = (news , (newval, fromList (map reachFor (agentsOf (GKM m))))) where
      newval = M.mapWithKey applyPC (fst $ m ! s)
      applyPC p oldbit
        | p `elem` M.keys (post (cm ! a)) = eval (GKM m,s) (post (cm ! a) ! p)
        | otherwise = oldbit
      reachFor i = (i, [ news' | ((s',a'),news') <- statePairs, s' `elem` snd (m !  s) ! i, a' `elem` rel (cm ! a) ! i ])
    newcur = fromJust $ lookup (oldcur,act) statePairs

publicMakeFalseChM :: [Agent] -> Prp -> PointedChangeModel
publicMakeFalseChM ags p = (ChM $ fromList [ (1::Action, Ch myPre myPost myRel) ], 0) where
  myPre = Top
  myPost = fromList [(p,Bot)]
  myRel = fromList [(i,[1]) | i <- ags]

instance KripkeLike PointedChangeModel where
  directed = const True
  getNodes (ChM cm, _) = map (show &&& labelOf) (M.keys cm) where
    labelOf a = "$\\begin{array}{c}\\\\" ++ tex (pre (cm ! a)) ++ "\\\\" ++ intercalate "\\\\\n" (map showPost (M.toList $ post (cm ! a))) ++ "\\end{array}$"
    showPost (p,f) = tex p ++ " := " ++ tex f
  getEdges (ChM cm, _) =
    concat [ [ (i, show a, show b) | b <- rel (cm ! a) ! i ] | a <- M.keys cm, i <- agentsOf (ChM cm) ]
  getActuals (_, a) = [show a]

instance TexAble PointedChangeModel where
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

type Event = (Transformer,State)

instance TexAble Transformer where
  tex (Trf addprops addlaw changeprops changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", "
    , tex addlaw, ", "
    , tex changeprops, ", "
    , intercalate ", " $ map snd . toList $ M.mapWithKey (\prop changebdd -> tex prop ++ " := " ++ tex (formOf changebdd)) changelaw, ", "
    , intercalate ", " eobddstrings
    , " \\right) \n"
    ] where
        eobddstrings = map (bddstring . (fst &&& (texRelBDD . snd))) (toList eventObs)
        bddstring (i,os) = "\\Omega^+_{\\text{" ++ i ++ "}} = " ++ bddprefix ++ os ++ bddsuffix

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", ", tex eventFacts, " \\right) \n" ]

-- TODO: this is horribly long, maybe split into several steps?
transform :: GenScenario -> Event -> GenScenario
transform (kns@(GenKnS props lawbdd obdds),s) (Trf addprops addlaw changeprops changelaw eventObs, eventFacts) =
  (GenKnS newprops newlawbdd newobs, news) where
    -- shift addprops to ensure props and newprops are disjoint:
    shiftaddprops = [(freshp props)..]
    shiftrel = zip addprops shiftaddprops
    shiftrelVars = map (over both fromEnum) shiftrel
    -- copies of modified propositions:
    copychangeprops = [(freshp $ props ++ map snd shiftrel)..]
    copyrel = zip changeprops copychangeprops
    copyrelVars = map (over both fromEnum) copyrel
    -- new vocabulary:
    newprops = props ++ map snd shiftrel ++ map snd copyrel
    -- new law:
    newlawbdd = con
      (relabel copyrelVars (con lawbdd (bddOf kns (replPsInF shiftrel addlaw))))
      (conSet [var (fromEnum q) `equ` relabel copyrelVars (relabel shiftrelVars $ changelaw ! q) | q <- changeprops])
    -- copies of modified propositions in double vocabulary:
    copyrelMV = zip (mv changeprops) (mv copychangeprops)
    copyrelCP = zip (cp changeprops) (cp copychangeprops)
    copyrelMVCPVars = if check
      then map (over both fromEnum) (copyrelMV ++ copyrelCP) -- TODO: remove assertion?
      else error "copyrelMV and copyrelCP are not disjoint!"
      where check = null (map fst copyrelMV `intersect` map fst copyrelCP)
                 && null (map snd copyrelMV `intersect` map snd copyrelCP)
    copyrelMVCP = relabel copyrelMVCPVars -- phew.
    -- shifted added propositions in double vocabulary:
    shiftrelMV = zip (mv addprops) (mv shiftaddprops)
    shiftrelCP = zip (cp addprops) (cp shiftaddprops)
    shiftrelMVCPVars = if null $ copyrelMV `intersect` copyrelCP
      then map (over both fromEnum) (shiftrelMV ++ shiftrelCP) -- TODO: remove assertion?
      else error "shiftrelMV and shiftrelCP are not disjoint!"
    shiftrelMVCP = relabel shiftrelMVCPVars -- phew.
    -- new observations: NOTE: we need to relabel eventObs with ????
    newobs = M.mapWithKey
      (\i oldobs -> con <$> (copyrelMVCP <$> oldobs) <*> (shiftrelMVCP <$> (eventObs ! i))) obdds
    -- new state:
    news = sort $ concat
      [ s \\ changeprops -- unchanged old props
      , map (apply copyrel) $ s `intersect` changeprops -- copies of modified props
      , map (apply shiftrel) eventFacts -- the actual event
      , filter (\ p -> bddEval s (changelaw ! p)) changeprops -- changed props now true
      ]

publicMakeFalse :: [Agent] -> Prp -> Event
publicMakeFalse agents p = (Trf [] Top [p] mychangelaw myobs, []) where
  mychangelaw = fromList [ (p,boolBddOf Bot) ]
  myobs = fromList [ (i,triviRelBdd) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalse (agentsOf $ fst SMCDEL.Other.NonS5.exampleStart) (SMCDEL.Language.P 0)

tResult :: GenScenario
tResult = SMCDEL.Other.NonS5.exampleStart `transform` myEvent

flipAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipAndShowTo everyone p i = (Trf [q] myeventlaw [p] mychangelaw myobs, [q])where
  q = freshp [p]
  myeventlaw = PrpF q `Equi` PrpF p
  mychangelaw = fromList [ (p, boolBddOf . Neg . PrpF $ p) ]
  myobs = fromList $
    (i, allsamebdd  [q]) :
    [ (j,triviRelBdd) | j <- everyone \\ [i] ]

myOtherEvent :: Event
myOtherEvent = flipAndShowTo ["1","2"] (P 0) "1"

tResult2 :: GenScenario
tResult2 = SMCDEL.Other.NonS5.exampleStart `transform` myOtherEvent

pp, qq, tt :: Prp
pp = P 0
tt = P 1
qq = P 7 -- this number should not matter!

sallyInit :: GenScenario
sallyInit = (GenKnS [pp, tt] law obs, actual) where
  law    = boolBddOf $ Conj [PrpF pp, Neg (PrpF tt)]
  obs    = fromList [ ("Sally", triviRelBdd), ("Anne", triviRelBdd) ]
  actual = [pp]

sallyPutsMarbleInBasket :: Event
sallyPutsMarbleInBasket = (Trf [] Top [tt]
  (fromList [ (tt,boolBddOf Top) ])
  (fromList [ (i,triviRelBdd) | i <- ["Anne","Sally"] ]), [])

sallyIntermediate1 :: GenScenario
sallyIntermediate1 = sallyInit `transform` sallyPutsMarbleInBasket

sallyLeaves :: Event
sallyLeaves = (Trf [] Top [pp]
  (fromList [ (pp,boolBddOf Bot) ])
  (fromList [ (i,triviRelBdd) | i <- ["Anne","Sally"] ]), [])

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
  (fromList [ (i,triviRelBdd) | i <- ["Anne","Sally"] ]), [])

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
