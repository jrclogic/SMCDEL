{-# LANGUAGE TemplateHaskell #-}

module SMCDEL.Internal.Files where

import Data.FileEmbed

import qualified Data.Text as T
import qualified Data.Text.Encoding as E

getFileContent :: String -> T.Text
getFileContent s = case s of
  "index.html"           -> E.decodeUtf8 $(embedFile "static/index.html")
  "MuddyChildren"        -> E.decodeUtf8 $(embedFile "Examples/MuddyChildren.smcdel.txt")
  "DiningCryptographers" -> E.decodeUtf8 $(embedFile "Examples/DiningCryptographers.smcdel.txt")
  "DrinkingLogicians"    -> E.decodeUtf8 $(embedFile "Examples/DrinkingLogicians.smcdel.txt")
  _                      -> error "File not found."
