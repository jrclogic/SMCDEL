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
import SMCDEL.Language
import Data.HasCacBDD.Visuals (svgGraph)

main :: IO ()
main = do
  putStrLn "Please open this link: http://localhost:3000/index.html"
  scotty 3000 $ do
    get "" $ redirect "index.html"
    get "/" $ redirect "index.html"
    get "/index.html" $ html $ T.fromStrict $ getFileContent "index.html"
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
        [ "<html><head>"
        , "<script type=\"text/x-mathjax-config\">MathJax.Hub.Config({ \"HTML-CSS\": { linebreaks: { automatic: true } }, SVG: { linebreaks: { automatic: true } } }); </script>"
        , "<script src='https://code.jquery.com/jquery-2.1.4.min.js'></script>"
        , "<script src='https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML'></script>"
        , "<script src='check.js'></script>"
        , "</head><body>"
        , T.pack knstring
        , "<hr />\n"
        , T.pack results
        , "</body></html>\n" ]

doJob :: KnowStruct -> Either Form Form -> String
doJob mykns (Left f) = unlines
  [ "\\( \\mathcal{F} "
  , if validViaBdd mykns f then "\\vDash" else "\\not\\vDash"
  , (texForm.simplify) f
  , "\\)" ]
doJob mykns (Right f) = unlines
  [ "The formula \\("
  , (texForm.simplify) f
  , "\\) is true at \\("
  , intercalate "," $ map texPropSet (whereViaBdd mykns f)
  , "\\)" ]

showStructure :: KnowStruct -> IO String
showStructure (KnS props lawbdd obs) = do
  svgString <- svgGraph lawbdd
  return $ "$$ \\mathcal{F} = \\left( \n"
    ++ texPropSet props ++ ", "
    ++ " \\begin{array}{l} {"++ " \\href{javascript:showlaw()}{\\theta} " ++"} \\end{array}\n "
    ++ ", \\begin{array}{l}\n"
    ++ intercalate " \\\\\n " (map (\(i,os) -> ("O_{"++i++"}=" ++ texPropSet os)) obs)
    ++ "\\end{array}\n"
    ++ " \\right) $$ \n <div class='lawbdd' style='display:none;'> where \\(\\theta\\) is this BDD:<br /><p align='center'>" ++ svgString ++ "</p></div>"
