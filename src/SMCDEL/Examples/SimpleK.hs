module SMCDEL.Examples.SimpleK where

import Data.HasCacBDD hiding (Bot,Top)
import Data.List ((\\))
import qualified Data.Map.Strict as M
import Data.Tagged (untag)

import SMCDEL.Explicit.K
import SMCDEL.Language
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Translations.K

exampleModel :: KripkeModel
exampleModel = KrM $ M.fromList
  [ (1, (M.fromList [(P 0,True ),(P 1,True )], M.fromList [(alice,[1]), (bob,[1])] ) )
  , (2, (M.fromList [(P 0,False),(P 1,True )], M.fromList [(alice,[1]), (bob,[2])] ) ) ]

examplePointedModel :: PointedModel
examplePointedModel = (exampleModel,1)

aliceBdd, bobBdd :: Bdd
[aliceBdd,bobBdd] = map (untag . flip SMCDEL.Symbolic.K.relBddOfIn exampleModel) [alice,bob]

-- Privately tell alice that P 0, while bob thinks nothing happens.
exampleGenActM :: ActionModel
exampleGenActM = ActM $ M.fromList
  [ (1, Act { pre = PrpF (P 0), post = M.empty, rel = M.fromList [(alice,[1]), (bob,[2])] } )
  , (2, Act { pre = Top       , post = M.empty, rel = M.fromList [(alice,[2]), (bob,[2])] } )
  ]

examplePointedActM :: PointedActionModel
examplePointedActM = (exampleGenActM,1)

exampleResult :: PointedModel
exampleResult = update examplePointedModel examplePointedActM

exampleStart :: BelScene
exampleStart = (BlS [P 0] law obs, actual) where
  law    = boolBddOf Top
  obs    = M.fromList [ ("1", mvBdd $ boolBddOf Top), ("2", allsamebdd [P 0]) ]
  actual = [P 0]

exampleEvent :: Event
exampleEvent = (Trf [P 1] addlaw M.empty eventObs, [P 1]) where
  addlaw = PrpF (P 1) `Impl` PrpF (P 0)
  eventObs = M.fromList [ ("1", allsamebdd [P 1]), ("2", cpBdd . boolBddOf $ Neg (PrpF $ P 1)) ]

exampleBlTresult :: BelScene
exampleBlTresult = exampleStart `update` exampleEvent

publicMakeFalseActM :: [Agent] -> Prp -> PointedActionModel
publicMakeFalseActM ags p =
  (ActM $ M.fromList [ (1::Int, Act myPre myPost myRel) ], 0) where
    myPre  = Top
    myPost = M.fromList [(p,Bot)]
    myRel  = M.fromList [(i,[1]) | i <- ags]

publicMakeFalseTrf :: [Agent] -> Prp -> Event
publicMakeFalseTrf agents p = (Trf [] Top changelaw eventobs, []) where
  changelaw = M.fromList [ (p,boolBddOf Bot) ]
  eventobs  = M.fromList [ (i,totalRelBdd) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalseTrf (agentsOf exampleStart) (P 0)

tResult :: BelScene
tResult = exampleStart `update` myEvent

flipOverAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipOverAndShowTo everyone p i = (Trf [q] eventlaw changelaw eventobs, [q]) where
  q         = freshp [p]
  eventlaw  = PrpF q `Equi` PrpF p
  changelaw = M.fromList [ (p, boolBddOf . Neg . PrpF $ p) ]
  eventobs  = M.fromList $ (i, allsamebdd [q])
                       : [ (j,totalRelBdd) | j <- everyone \\ [i] ]

myOtherEvent :: Event
myOtherEvent = flipOverAndShowTo ["1","2"] (P 0) "1"

tResult2 :: BelScene
tResult2 = exampleStart `update` myOtherEvent

exampleBelScn :: BelScene
exampleBelScn = kripkeToBls examplePointedModel
