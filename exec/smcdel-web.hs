{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module Main where

import Prelude
import Control.Monad.IO.Class (liftIO)
import Control.Arrow
import Data.FileEmbed
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Version (showVersion)
import Paths_smcdel (version)
import Web.Scotty
import qualified Data.Text as T
import qualified Data.Text.Encoding as E
import qualified Data.Text.Lazy as TL
import Data.HasCacBDD.Visuals (svgGraph)
import qualified Language.Javascript.JQuery as JQuery
import Language.Haskell.TH.Syntax
import Network.Wai.Handler.Warp (defaultSettings, setHost, setPort)
import System.Environment (lookupEnv)
import Text.Read (readMaybe)

import SMCDEL.Internal.Lex
import SMCDEL.Internal.Parse
import SMCDEL.Symbolic.S5
import SMCDEL.Internal.TexDisplay
import SMCDEL.Translations.S5
import SMCDEL.Language

main :: IO ()
main = do
  putStrLn $ "SMCDEL " ++ showVersion version ++ " -- https://github.com/jrclogic/SMCDEL"
  port <- fromMaybe 3000 . (readMaybe =<<) <$> lookupEnv "PORT"
  putStrLn $ "Please open this link: http://127.0.0.1:" ++ show port ++ "/index.html"
  let mySettings = Options 1 (setHost "127.0.0.1" $ setPort port defaultSettings)
  scottyOpts mySettings $ do
    get "" $ redirect "index.html"
    get "/" $ redirect "index.html"
    get "/index.html"  . html . TL.fromStrict $ addVersionNumber $ embeddedFile "index.html"
    get "/jquery.js"   . html . TL.fromStrict $ embeddedFile "jquery.js"
    get "/ace.js"      . html . TL.fromStrict $ embeddedFile "ace.js"
    get "/viz-lite.js" . html . TL.fromStrict $ embeddedFile "viz-lite.js"
    get "/getExample" $ do
      this <- param "filename"
      html . TL.fromStrict $ embeddedFile this
    post "/check" $ do
      smcinput <- param "smcinput"
      case alexScanTokensSafe smcinput of
        Left pos -> webError "Lex" pos
        Right lexResult -> case parse lexResult of
          Left pos -> webError "Parse" pos
          Right (CheckInput vocabInts lawform obs jobs) -> do
            let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
            knstring <- liftIO $ showStructure mykns
            let results = concatMap (\j -> "<p>" ++ doJobWeb mykns j ++ "</p>") jobs
            html $ mconcat
              [ TL.pack knstring
              , "<hr />\n"
              , TL.pack results ]
    post "/knsToKripke" $ do
      smcinput <- param "smcinput"
      case alexScanTokensSafe smcinput of
        Left pos -> webError "Lex" pos
        Right lexResult -> case parse lexResult of
          Left pos -> webError "Parse" pos
          Right (CheckInput vocabInts lawform obs _) -> do
            let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
            _ <- liftIO $ showStructure mykns -- this moves parse errors to scotty
            if numberOfStates mykns > 32
              then html . TL.pack $ "Sorry, I will not draw " ++ show (numberOfStates mykns) ++ " states!"
              else do
                let (myKripke, _) = knsToKripke (mykns, head $ statesOf mykns) -- ignore actual world
                html $ TL.concat
                  [ TL.pack "<div id='here'></div>"
                  , TL.pack "<script>document.getElementById('here').innerHTML += Viz('"
                  , fixTeXinSVG $ textDot myKripke
                  , TL.pack "');</script>" ]

fixTeXinSVG :: TL.Text -> TL.Text
fixTeXinSVG = TL.replace "$" ""
  . TL.replace "p_{" " "
  . TL.replace "} " " "

doJobWeb :: KnowStruct -> Job -> String
doJobWeb mykns (TrueQ s f) = unlines
  [ "\\( (\\mathcal{F}, " ++ sStr ++ " ) "
  , if evalViaBdd (mykns, map P s) f then "\\vDash" else "\\not\\vDash"
  , (texForm . simplify) f
  , "\\)" ] where sStr = " \\{ " ++ intercalate "," (map (\i -> "p_{" ++ show i ++ "}") s) ++ " \\}"
doJobWeb mykns (ValidQ f) = unlines
  [ "\\( \\mathcal{F} "
  , if validViaBdd mykns f then "\\vDash" else "\\not\\vDash"
  , (texForm . simplify) f
  , "\\)" ]
doJobWeb mykns (WhereQ f) = unlines
  [ "At which states is \\("
  , (texForm . simplify) f
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
    ++ intercalate " \\\\\n " (map (\(i,os) -> "O_{"++i++"}=" ++ tex os) obs)
    ++ "\\end{array}\n"
    ++ " \\right) $$ \n <div class='lawbdd' style='display:none;'> where \\(\\theta\\) is this BDD:<br /><p align='center'>" ++ svgString ++ "</p></div>"

embeddedFile :: String -> T.Text
embeddedFile s = case s of
  "index.html"           -> E.decodeUtf8 $(embedFile "static/index.html")
  "viz-lite.js"          -> E.decodeUtf8 $(embedFile "static/viz-lite.js")
  "ace.js"               -> E.decodeUtf8 $(embedFile "static/ace.js")
  "jquery.js"            -> E.decodeUtf8 $(embedFile =<< runIO JQuery.file)
  "MuddyChildren"        -> E.decodeUtf8 $(embedFile "Examples/MuddyChildren.smcdel.txt")
  "DiningCryptographers" -> E.decodeUtf8 $(embedFile "Examples/DiningCryptographers.smcdel.txt")
  "DrinkingLogicians"    -> E.decodeUtf8 $(embedFile "Examples/DrinkingLogicians.smcdel.txt")
  "CherylsBirthday"      -> E.decodeUtf8 $(embedFile "Examples/CherylsBirthday.smcdel.txt")
  _                      -> error "File not found."

addVersionNumber :: T.Text -> T.Text
addVersionNumber = T.replace "<!-- VERSION NUMBER -->" (T.pack $ showVersion version)

webError :: String -> (Int,Int) -> ActionM ()
webError kind (lin,col) = html $ TL.pack $ concat
  [ "<p class='error'>", kind, " error in line ", show lin, ", column ", show col, "</p>\n"
  , "<script>"
  , "editor.clearSelection();"
  , "editor.moveCursorTo(", show (lin - 1), ",", show col, ");"
  , "editor.renderer.scrollCursorIntoView({row: ", show (lin - 1),", column: ", show col, "}, 0.5);"
  , "editor.focus();"
  , "</script>"
  ]
