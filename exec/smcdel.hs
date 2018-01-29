module Main where

import Control.Arrow (second)
import Control.Monad (when,unless)
import Data.List (intercalate)
import System.Console.ANSI
import System.Directory (getTemporaryDirectory)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure)
import System.Process (system)
import System.FilePath.Posix (takeBaseName)
import System.IO (Handle,hClose,hPutStrLn,stderr,stdout,openTempFile)
import SMCDEL.Internal.Lex
import SMCDEL.Internal.Parse
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5

main :: IO ()
main = do
  (input,options) <- getInputAndSettings
  let showMode = "-show" `elem` options
  let texMode = "-tex" `elem` options || showMode
  tmpdir <- getTemporaryDirectory
  (texFilePath,texFileHandle) <- openTempFile tmpdir "smcdel.tex"
  let outHandle = if showMode then texFileHandle else stdout
  unless texMode $ vividPutStrLn infoline
  when texMode $ hPutStrLn outHandle texPrelude
  let (CheckInput vocabInts lawform obs jobs) = parse $ alexScanTokens input
  let mykns = KnS (map P vocabInts) (boolBddOf lawform) (map (second (map P)) obs)
  when texMode $
    hPutStrLn outHandle $ unlines
      [ "\\section{Given Knowledge Structure}", "\\[ (\\mathcal{F},s) = (" ++ tex ((mykns,[])::KnowScene) ++ ") \\]", "\\section{Results}" ]
  mapM_ (doJob outHandle texMode mykns) jobs
  when texMode $ hPutStrLn outHandle texEnd
  when showMode $ do
    hClose outHandle
    let command = "cd /tmp && pdflatex -interaction=nonstopmode " ++ takeBaseName texFilePath ++ ".tex > " ++ takeBaseName texFilePath ++ ".pdflatex.log && xdg-open "++ takeBaseName texFilePath ++ ".pdf"
    putStrLn $ "Now running: " ++ command
    _ <- system command
    return ()
  putStrLn "\nDoei!"

doJob :: Handle -> Bool -> KnowStruct -> Job -> IO ()
doJob outHandle True mykns (ValidQ f) = do
  hPutStrLn outHandle $ "Is $" ++ texForm (simplify f) ++ "$ valid on $\\mathcal{F}$?"
  hPutStrLn outHandle (show (validViaBdd mykns f) ++ "\n\n")
doJob outHandle False mykns (ValidQ f) = do
  hPutStrLn outHandle $ "Is " ++ ppForm f ++ " valid on the given structure?"
  vividPutStrLn (show (validViaBdd mykns f) ++ "\n")
doJob outHandle True mykns (WhereQ f) = do
  hPutStrLn outHandle $ "At which states is $" ++ texForm (simplify f) ++ "$ true? $"
  let states = map tex (whereViaBdd mykns f)
  hPutStrLn outHandle $ intercalate "," states
  hPutStrLn outHandle "$\n"
doJob outHandle False mykns (WhereQ f) = do
  hPutStrLn outHandle $ "At which states is " ++ ppForm f ++ " true?"
  mapM_ (vividPutStrLn.show.map(\(P n) -> n)) (whereViaBdd mykns f)
  putStr "\n"

getInputAndSettings :: IO (String,[String])
getInputAndSettings = do
  args <- getArgs
  case args of
    ("-":options) -> do
      input <- getContents
      return (input,options)
    (filename:options) -> do
      input <- readFile filename
      return (input,options)
    _ -> do
      name <- getProgName
      mapM_ (hPutStrLn stderr)
        [ infoline
        , "usage: " ++ name ++ " <filename> {options}"
        , "       (use filename - for STDIN)\n"
        , "  -tex   generate LaTeX code\n"
        , "  -show  write to /tmp, generate PDF and show it (implies -tex)\n" ]
      exitFailure

vividPutStrLn :: String -> IO ()
vividPutStrLn s = do
  setSGR [SetColor Foreground Vivid White]
  putStrLn s
  setSGR []

infoline :: String
infoline = "SMCDEL 16.5 by Malvin Gattinger -- https://github.com/jrclogic/SMCDEL\n"

texPrelude, texEnd :: String
texPrelude = unlines [ "\\documentclass[a4paper,12pt]{article}",
  "\\usepackage{amsmath,amssymb,tikz,graphicx,color,etex,datetime,setspace,latexsym}",
  "\\usepackage[margin=2cm]{geometry}",
  "\\usepackage[T1]{fontenc}", "\\parindent0cm", "\\parskip1em",
  "\\usepackage{hyperref}",
  "\\hypersetup{pdfborder={0 0 0}}",
  "\\title{Results}",
  "\\author{\\href{https://github.com/jrclogic/SMCDEL}{SMCDEL}}",
  "\\begin{document}",
  "\\maketitle" ]
texEnd = "\\end{document}"
