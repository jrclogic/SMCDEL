module Main (main) where

import Control.Monad (filterM, forM)
import Data.List ((\\))
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension)
import Test.DocTest

main :: IO ()
main = do
  flist <- collectFiles "./src/"
  doctest $
    [ "-isrc"
    -- , "--verbose"
    , "--fast"
    , "-Wno-x-partial"
    ] ++ (flist \\ exclude)

exclude :: [FilePath]
exclude =
  [ "./src/SMCDEL/Internal/MyHaskCUDD.hs"
  , "./src/SMCDEL/Symbolic/S5_CUDD.hs"
  , "./src/SMCDEL/Symbolic/K_CUDD.hs"
  , "./src/SMCDEL/Symbolic/Ki_CUDD.hs"
  , "./src/SMCDEL/Internal/MyHaskCUDD.hs"
  , "./src/SMCDEL/Examples/SumAndProduct/General.hs"
  , "./src/SMCDEL/Examples/DiningCrypto/General.hs"
  ]

collectFiles :: FilePath -> IO [FilePath]
collectFiles dir = do
  contents <- listDirectory dir
  let paths = map (dir </>) contents
  files <- filterM doesDirectoryExist paths
  let hsFiles = filter (\p -> takeExtension p `elem` [".hs", ".lhs"]) paths
  subDirFiles <- forM files collectFiles
  return $ hsFiles ++ concat subDirFiles
