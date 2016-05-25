{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prelude
import Control.Monad.IO.Class (liftIO)
import Control.Arrow
import Data.List (intercalate)
import Web.Scotty
import qualified Data.Text.Lazy as T
import SMCDEL.Internal.Lex
import SMCDEL.Internal.Parse
import SMCDEL.Internal.Files
import SMCDEL.Symbolic.HasCacBDD
import SMCDEL.Internal.TexDisplay
import SMCDEL.Translations
import SMCDEL.Language
import Data.HasCacBDD.Visuals (svgGraph)

main :: IO ()
main = do
  putStrLn "Please open this link: http://localhost:3000/index.html"
  scotty 3000 $ do
    get "" $ redirect "index.html"
    get "/" $ redirect "index.html"
    get "/index.html" $ html $ T.fromStrict $ getFileContent "index.html"
    get "/getExample" $ do
      this <- param "filename"
      html $ T.fromStrict $ getFileContent this
    post "/check" $ do
      smcinput <- param "smcinput"
      let (CheckInput vocabInts lawform obs jobs) = parse $ alexScanTokens smcinput
      let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
      knstring <- liftIO $ showStructure mykns
      let results = concatMap (\j -> "<p>" ++ doJob mykns j ++ "</p>") jobs
      html $ mconcat
        [ T.pack knstring
        , "<hr />\n"
        , T.pack results ]
    post "/knsToKripke" $ do
      smcinput <- param "smcinput"
      let (CheckInput vocabInts lawform obs _) = parse $ alexScanTokens smcinput
      let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
      _ <- liftIO $ showStructure mykns -- this moves parse errors to scotty
      if numberOfStates mykns > 20
        then html $ T.pack $ "Sorry, I will not draw " ++ show (numberOfStates mykns) ++ " states!"
        else do
          let myKripke = knsToKripke (mykns, head $ statesOf mykns) -- FIXME: how to pick actual world?
          html $ T.pack ("<p>" ++ svg myKripke ++ "</p>")

-- FIXME: merge with doJob in MainCLI.hs
doJob :: KnowStruct -> Either Form Form -> String
doJob mykns (Left f) = unlines
  [ "\\( \\mathcal{F} "
  , if validViaBdd mykns f then "\\vDash" else "\\not\\vDash"
  , (texForm.simplify) f
  , "\\)" ]
doJob mykns (Right f) = unlines
  [ "At which states is \\("
  , (texForm.simplify) f
  , "\\) true?<br /> \\("
  , intercalate "," $ map tex (whereViaBdd mykns f)
  , "\\)" ]

showStructure :: KnowStruct -> IO String
showStructure (KnS props lawbdd obs) = do
  svgString <- svgGraph lawbdd
  return $ "$$ \\mathcal{F} = \\left( \n"
    ++ tex props ++ ", "
    ++ " \\begin{array}{l} {"++ " \\href{javascript:toggleLaw()}{\\theta} " ++"} \\end{array}\n "
    ++ ", \\begin{array}{l}\n"
    ++ intercalate " \\\\\n " (map (\(i,os) -> ("O_{"++i++"}=" ++ tex os)) obs)
    ++ "\\end{array}\n"
    ++ " \\right) $$ \n <div class='lawbdd' style='display:none;'> where \\(\\theta\\) is this BDD:<br /><p align='center'>" ++ svgString ++ "</p></div>"
