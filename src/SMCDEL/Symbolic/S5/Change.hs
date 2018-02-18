
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module SMCDEL.Symbolic.S5.Change where

import Control.Lens (over,both)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

import SMCDEL.Language
import SMCDEL.Internal.TexDisplay
import SMCDEL.Other.BDD2Form
import SMCDEL.Internal.Help (apply,applyPartial)
import SMCDEL.Symbolic.S5 hiding (Event)

data KnowChange = CTrf
  [Prp]               -- addprops
  Form                -- event law
  [Prp]               -- changeprops, modified subset
  (M.Map Prp Bdd)     -- changelaw
  (M.Map Agent [Prp]) -- eventObs
  deriving (Show)

instance HasAgents KnowChange where
  agentsOf (CTrf _ _ _ _ obdds) = M.keys obdds

type Event = (KnowChange,State)

instance HasAgents Event where
  agentsOf = agentsOf . fst

type MultiEvent = (KnowChange,[State])

instance TexAble KnowChange where
  tex (CTrf addprops addlaw changeprops changelaw eventObs) = concat
    [ " \\left( \n"
    , tex addprops, ", \\ "
    , tex addlaw, ", \\ "
    , tex changeprops, ", \\ "
    , intercalate ", " $ map snd . M.toList $ M.mapWithKey texChange changelaw
    , ", \\ \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> (tex os)) (M.toList eventObs))
    , "\\end{array}\n"
    , " \\right) \n"
    ] where
        texChange prop changebdd = tex prop ++ " := " ++ tex (formOf changebdd)

instance TexAble Event where
  tex (trf, eventFacts) = concat
    [ " \\left( \n", tex trf, ", \\ ", tex eventFacts, " \\right) \n" ]

knowChange :: KnowScene -> Event -> KnowScene
knowChange (kns@(KnS props law obs),s) (CTrf addprops addlaw changeprops changelaw eventObs, eventFacts) =
  (KnS newprops newlaw newobs, news) where
    relabelWith r = relabel (sort $ map (over both fromEnum) r)
    -- PART 1: SHIFTING addprops to ensure props and newprops are disjoint
    shiftrel = sort $ zip addprops [(freshp props)..]
    shiftaddprops = map snd shiftrel
    -- apply the shifting to addlaw, changelaw and eventObs:
    addlawShifted    = replPsInF shiftrel addlaw
    changelawShifted = M.map (relabelWith shiftrel) changelaw
    eventObsShifted  = M.map (map (apply shiftrel)) eventObs
    -- the actual event:
    x = map (apply shiftrel) eventFacts
    -- PART 2: COPYING the modified propositions
    copyrel = zip changeprops [(freshp $ props ++ shiftaddprops)..]
    copychangeprops = map snd copyrel
    newprops = sort $ props ++ shiftaddprops ++ copychangeprops -- V ∪ V⁺ ∪ V°
    newlaw = conSet $ relabelWith copyrel (con law (bddOf kns addlawShifted))
                    : [var (fromEnum q) `equ` relabelWith copyrel (changelawShifted ! q) | q <- changeprops]
    newobs = [ (i , sort $ map (applyPartial copyrel) (apply obs i) ++ eventObsShifted ! i) | i <- map fst obs ]
    news | bddEval (s ++ x) (con law (bddOf kns addlawShifted)) = sort $ concat
            [ s \\ changeprops
            , map (apply copyrel) $ s `intersect` changeprops
            , x
            , filter (\ p -> bddEval (s ++ x) (changelawShifted ! p)) changeprops ]
         | otherwise = error "Transformer is not applicable!"

myStart :: KnowScene
myStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])

publicMakeFalse :: [Agent] -> Prp -> Event
publicMakeFalse agents p = (CTrf [] Top [p] mychangelaw myobs, []) where
  mychangelaw = M.fromList [ (p,boolBddOf Bot) ]
  myobs = M.fromList [ (i,[]) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalse (agentsOf myStart) (P 0)

myResult :: KnowScene
myResult = myStart `knowChange` myEvent

exampleStart :: KnowScene
exampleStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])

makeFalseShowTo :: [Agent] -> Prp -> [Agent] -> Event
makeFalseShowTo agents p intheknow = (CTrf [P 99] Top [p] examplechangelaw exampleobs, []) where
  examplechangelaw = M.fromList [ (p,boolBddOf $ PrpF (P 99)) ]
  exampleobs = M.fromList $ [ (i,[P 99]) | i <- intheknow           ]
                         ++ [ (i,[    ]) | i <- agents \\ intheknow ]

exampleEvent :: Event
exampleEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Bob"]

exampleResult :: KnowScene
exampleResult = exampleStart `knowChange` exampleEvent

thirdEvent :: Event
thirdEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Alice"]

thirdResult :: KnowScene
thirdResult = exampleStart `knowChange` thirdEvent
