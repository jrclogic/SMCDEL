{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Main (main) where

import qualified Data.Map.Strict as M
import Test.Hspec
import Test.Hspec.QuickCheck

import SMCDEL.Internal.Help (alleq)
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD (Manager, makeManagerZ)
import SMCDEL.Internal.MyHaskCUDD (Z, B, F0, F1, S0, S1, DdCtx)
import SMCDEL.Language
import qualified SMCDEL.Symbolic.Ki_CUDD as Cudd
import qualified SMCDEL.Symbolic.S5_CUDD as CuddBase

main :: IO ()
main = do
  mgr <- MyHaskCUDD.makeManagerZ 20
  hspec $ do
    describe "hardcoded myScn" $ do
      prop "all DD kinds" $ alleq . ddKindTest mgr

myKnS :: (DdCtx a b c) => MyHaskCUDD.Manager -> Cudd.BelStruct a b c
myKnS mgr = Cudd.BlS mgr myDefaultProps (CuddBase.boolDdOf mgr Top) (myDefaultObservables mgr)

--myKnScac :: Cac.BelStruct
--myKnScac = Cac.BlS myDefaultProps (CacBase.boolBddOf Top) myDefaultObservables

myDefaultState :: [Prp]
myDefaultState = [P 0 .. P 4]

myDefaultProps :: [Prp]
myDefaultProps = [P 0 .. P 4]

myDefaultObservables :: (DdCtx a b c) => MyHaskCUDD.Manager -> (M.Map Agent Int, Cudd.RelDD a b c)
myDefaultObservables mgr = (M.fromList [("1", 0), ("2", 1), ("3",2), ("4",3), ("5",4)], (pure $ CuddBase.boolDdOf mgr $ Conj [
    Impl (PrpF $ P 0) (Conj (zipWith Equi (map PrpF [P 5, P 7, P 9, P 11]) (map PrpF [P 6, P 8, P 10, P 12]))),
    Impl (PrpF $ P 1) (Conj (zipWith Equi (map PrpF [P 5, P 7]) (map PrpF [P 6, P 8]))),
    Impl (PrpF $ P 2) (Bot),
    Impl (PrpF $ P 3) (PrpF $ P 5),
    Impl (PrpF $ P 4) (Top)
    ]))

ddKindTest :: MyHaskCUDD.Manager -> SimplifiedForm -> [Bool]
ddKindTest mgr (SF f) =
  [
    -- todo include Cac here?
    --Cac.evalViaBdd (myKnScac, myDefaultState) f
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene B F1 S1) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene B F1 S0) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene B F0 S1) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene B F0 S0) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene Z F1 S1) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene Z F1 S0) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene Z F0 S1) f,
    Cudd.evalViaDd ((myKnS mgr, myDefaultState) :: Cudd.BelScene Z F0 S0) f
  ]
