module Main where

-- import Data.List
import SMCDEL.Examples
-- import SMCDEL.Language
import SMCDEL.Translations
import SMCDEL.Symbolic.HasCacBDD
import SMCDEL.Explicit.Simple

main :: IO ()
main = do
  -- the basic plan still works?
  print $ basicPlan `succeedsOn` rusSCN

  print $ statesOf (fst rusSCN) == statesOf (fst $ rusSCNfor (3,3,1))

  print $ rusSCN == rusSCNfor (3,3,1)

  print $ basicPlan `succeedsOn` rusSCNfor (3,3,1)

  let mycheck c = mapM_ (print . fst) $ filter snd $ checkHandsFor c

  putStrLn "Two-step solutions for (2,2,1)"
  mycheck (2,2,1)

  putStrLn "Two-step solutions for (3,2,1)"
  mycheck (3,2,1)

  putStrLn "Two-step solutions for (3,3,1)"
  mycheck (3,3,1)

  putStrLn "Two-step solutions for (3,3,2)"
  mycheck (3,3,2)

  -- print rcSolutions

main2 :: IO ()
main2 = do
  putStrLn "Are this pointed model and this knowledge structure related?"
  print modelB
  print knsB
  case findStateMap modelB knsB of
    Nothing -> putStrLn "No, could not find a StateMap linking them."
    Just g -> do
      putStrLn "Yes, via this StateMap:"
      mapM_ print [ (w,g w) | w <- ws ] where (KrM ws _ _ ,_) = modelB
