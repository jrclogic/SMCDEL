
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Symbolic.K.Change where

import Control.Arrow ((&&&))
import Control.Lens (over,both)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),intersect,intercalate,sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!),fromList,toList)

import SMCDEL.Internal.Help (apply,powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Translations.S5 (booloutof)
import SMCDEL.Other.BDD2Form
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (bddEval,boolBddOf,State)

data Transformer = Trf
  [Prp] -- addprops
  Form  -- event law
  [Prp] -- changeprops, modified subset
  (M.Map Prp Bdd) -- changelaw
  (M.Map Agent RelBDD) -- eventObs
  deriving (Eq,Show)

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ _ obdds) = M.keys obdds

type Event = (Transformer,State)

type MultiEvent = (Transformer,[State])

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

transform :: BelScene -> Event -> BelScene
transform (kns@(BlS props law obdds),s) (Trf addprops addlaw changeprops changelaw eventObs, eventFacts) =
  (BlS newprops newlaw newobs, news) where
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    shiftaddprops = [(freshp props)..]
    shiftrel = sort $ zip addprops shiftaddprops
    relabelWith r = relabel (sort $ map (over both fromEnum) r)
    -- apply the shifting to addlaw and changelaw:
    addlawShifted = replPsInF shiftrel addlaw
    changelawShifted = M.map (relabelWith shiftrel) changelaw
    -- to apply the shifting to eventObs we need shiftrel for the double vocabulary:
    shiftrelMVCP = sort $ zip (mv addprops) (mv shiftaddprops)
                       ++ zip (cp addprops) (cp shiftaddprops)
    eventObsShifted = M.map (fmap $ relabelWith shiftrelMVCP) eventObs
    -- the actual event:
    x = map (apply shiftrel) eventFacts
    -- PART 2: COPYING the modified propositions
    copychangeprops = [(freshp $ props ++ map snd shiftrel)..]
    copyrel = zip changeprops copychangeprops
    copyrelMVCP = sort $ zip (mv changeprops) (mv copychangeprops)
    -- PART 3: actual transformation
    newprops = sort $ props ++ map snd shiftrel ++ map snd copyrel
    newlaw = conSet $ relabelWith copyrel (con law (bddOf kns addlawShifted))
                    : [var (fromEnum q) `equ` relabelWith copyrel (changelawShifted ! q) | q <- changeprops]
    newobs = M.mapWithKey (\i oldobs -> con <$> (relabelWith copyrelMVCP <$> oldobs) <*> (eventObsShifted ! i)) obdds
    news | bddEval (s ++ x) (con law (bddOf kns addlawShifted)) = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , x
            , filter (\ p -> bddEval (s ++ x) (changelawShifted ! p)) changeprops ]
         | otherwise = error "Transformer is not applicable!"

transformMulti :: BelScene -> MultiEvent -> BelScene
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
myEvent = publicMakeFalse (agentsOf $ fst SMCDEL.Symbolic.K.exampleStart) (P 0)

tResult :: BelScene
tResult = SMCDEL.Symbolic.K.exampleStart `transform` myEvent

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

tResult2 :: BelScene
tResult2 = SMCDEL.Symbolic.K.exampleStart `transform` myOtherEvent

trfPre :: Event -> Form
trfPre (Trf addprops addlaw _ _ _, x) = substitOutOf x addprops addlaw

trfPost :: Event -> Prp -> Bdd
trfPost (Trf addprops _ _ changelaw _, x) p
  | p `elem` M.keys changelaw = restrictLaw (changelaw ! p) (booloutof x addprops)
  | otherwise                 = boolBddOf $ PrpF p

reduce :: Event -> Form -> Maybe Form
reduce _ Top          = Just Top
reduce e Bot          = Just $ Neg $ trfPre e
reduce e (PrpF p)     = Impl (trfPre e) <$> Just (formOf $ trfPost e p)
reduce e (Neg f)      = Impl (trfPre e) <$> (Neg <$> reduce e f)
reduce e (Conj fs)    = Conj <$> mapM (reduce e) fs
reduce e (Disj fs)    = Disj <$> mapM (reduce e) fs
reduce e (Xor fs)     = Impl (trfPre e) <$> (Xor <$> mapM (reduce e) fs)
reduce e (Impl f1 f2) = Impl <$> reduce e f1 <*> reduce e f2
reduce e (Equi f1 f2) = Equi <$> reduce e f1 <*> reduce e f2
reduce _ (Forall _ _) = Nothing
reduce _ (Exists _ _) = Nothing
reduce e@(t@(Trf addprops _ _ _ eventObs), x) (K a f) =
  Impl (trfPre e) <$> (Conj <$> sequence
    [ K a <$> reduce (t,y) f | y <- powerset addprops -- FIXME is this a bit much?
                             , tagBddEval (mv x ++ cp y) (eventObs ! a)
    ])
reduce e (Kw a f)     = reduce e (Disj [K a f, K a (Neg f)])
reduce _ Ck  {}       = Nothing
reduce _ Ckw {}       = Nothing
reduce _ PubAnnounce  {} = Nothing
reduce _ PubAnnounceW {} = Nothing
reduce _ Announce     {} = Nothing
reduce _ AnnounceW    {} = Nothing
