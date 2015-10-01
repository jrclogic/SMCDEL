
module Main where
import Control.Arrow (second)
import Control.Monad (when,unless)
import System.Console.ANSI
import System.Directory (getTemporaryDirectory)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure)
import System.Process (system)
import System.FilePath.Posix (takeBaseName)
import System.IO (Handle,hClose,hPutStrLn,stderr,stdout,openTempFile)
import Lex
import Parse
import DELLANG
import KNSCAC
import Data.List (intercalate)

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
  when texMode $ do
    foo <- getTexStructure (mykns,[])
    hPutStrLn outHandle $ unlines
      [ "\\section{Given Knowledge Structure}", "\\[ (\\mathcal{F},s) = (" ++ foo ++ ") \\]", "\\section{Results}" ]
  mapM_ (doJob outHandle texMode mykns) jobs
  when texMode $ hPutStrLn outHandle texEnd
  when showMode $ do
    hClose outHandle
    _ <- system ("cd /tmp && pdflatex -interaction=nonstopmode " ++ takeBaseName texFilePath ++ ".tex > " ++ takeBaseName texFilePath ++ ".pdflatex.log && xdg-open "++ takeBaseName texFilePath ++ ".pdf")
    return ()
  putStrLn "\nDoei!"

doJob :: Handle -> Bool -> KnowStruct -> Either Form Form -> IO ()
doJob outHandle texMode mykns (Left f) =
  if texMode
  then do
    hPutStrLn outHandle $ "\\[" ++ texForm (simplify f) ++ "\\]"
    hPutStrLn outHandle "Is this valid on the given structure?"
    hPutStrLn outHandle (show (validViaBdd mykns f) ++ "\n")
  else do
    hPutStrLn outHandle $ "Is " ++ show f ++ " valid on the given structure?"
    vividPutStrLn (show (validViaBdd mykns f) ++ "\n")
doJob outHandle texMode mykns (Right f) = do
  if texMode
    then do
      hPutStrLn outHandle $ "\\[" ++ texForm (simplify f) ++ "\\]"
      hPutStrLn outHandle "At which states is this true? $"
      let states = map texPropSet (whereViaBdd mykns f)
      hPutStrLn outHandle $ intercalate "," states
      hPutStrLn outHandle "$"
    else do
      hPutStrLn outHandle $ "At which states is " ++ show f ++ " true?"
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
      hPutStrLn stderr infoline
      hPutStrLn stderr $ "usage: " ++ name ++ " <filename> {Options}"
      hPutStrLn stderr $ "       (use filename " ++ name ++ " -  to read STDIN)"
      hPutStrLn stderr ""
      hPutStrLn stderr "  -tex   Output will be LaTeX code"
      hPutStrLn stderr ""
      hPutStrLn stderr "  -show  Write output to /tmp, generate PDF and show it."
      hPutStrLn stderr "         (implies -tex)"
      exitFailure

vividPutStrLn :: String -> IO ()
vividPutStrLn s = do
  setSGR [SetColor Foreground Vivid White]
  putStrLn s
  setSGR []

infoline :: String
infoline = "SMCDEL 1.0 by Malvin Gattinger -- https://github.com/jrclogic/SMCDEL\n"

texPrelude, texEnd :: String
texPrelude = unlines [ "\\documentclass[a4paper,12pt]{article}",
  "\\usepackage{amsmath,amssymb,tikz,graphicx,color,etex,datetime,setspace,latexsym}",
  "\\usepackage[margin=2cm]{geometry}", "\\usepackage[T1]{fontenc}", "\\parindent0cm",
  "\\title{Results}", "\\author{SMCDEL}", "\\begin{document}", "\\maketitle" ]
texEnd = "\\end{document}"
