{-# LANGUAGE FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, AllowAmbiguousTypes, OverloadedStrings #-}

module SMCDEL.Internal.TexDisplay where
import Control.Monad
import Data.List
import qualified Data.Text.Lazy as T
import System.IO
import System.IO.Temp
import System.IO.Unsafe
import System.Process
import Data.GraphViz
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Types.Monadic

begintab, endtab, newline :: String
begintab  = "\\\\begin{tabular}{c}"
endtab    = "\\\\end{tabular}"
newline   = " \\\\\\\\[0pt] "

class TexAble a where
  tex :: a -> String
  texTo :: a -> String -> IO ()
  texTo x filename = writeFile (filename++".tex") (tex x)
  texDocumentTo :: a -> String -> IO ()
  texDocumentTo x filename =
    writeFile (filename++".tex") (pre ++ tex x ++ post) where
      pre = concat [ "\\documentclass[a4paper,10pt]{article}"
                   , "\\usepackage[utf8]{inputenc}"
                   , "\\usepackage{tikz,fontenc,graphicx}"
                   , "\\usepackage[pdftex]{hyperref}"
                   , "\\usepackage[margin=1cm]{geometry}"
                   , "\\hypersetup{pdfborder={0 0 0},breaklinks=true}"
                   , "\\begin{document}"
                   , "\\thispagestyle{none}" ]
      post= "\\end{document}"
  pdfTo :: a -> String -> IO ()
  pdfTo x filename = do
    texDocumentTo x filename
    runAndWait $ "cd " ++ filename ++ "/../; /usr/bin/pdflatex -interaction=nonstopmode "++filename++".tex"
  disp :: a -> IO ()
  disp x = withSystemTempDirectory "smcdel" $ \tmpdir -> do
    pdfTo x (tmpdir ++ "/temp")
    runIgnoreAndWait $ "/usr/bin/okular " ++ tmpdir ++ "/temp.pdf"
  svgViaTex :: a -> String
  svgViaTex x = unsafePerformIO $ withSystemTempDirectory "smcdel" $ \tmpdir -> do
    let filename = tmpdir ++ "/temp"
    pdfTo x filename
    runAndWait $ "pdftocairo -nocrop -svg "++filename++".pdf "++filename++".svg"
    readFile (filename ++ ".svg")

instance TexAble String where
  tex i = " \\text{" ++ i ++ "} "

instance TexAble Int where
  tex = show

-- | TeXing assignments as sets
instance TexAble a => TexAble [(a,Bool)] where
  tex ass = case filter snd ass of
    [] -> ""
    ps -> "$" ++ intercalate "," (map (tex.fst) ps) ++ "$"

runAndWait :: String -> IO ()
runAndWait command = do
  (_inp,_out,err,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  hGetContents err >>= (\x -> unless (null x) (putStrLn x))
  return ()

runIgnoreAndWait :: String -> IO ()
runIgnoreAndWait command = do
  (_inp,_out,_err,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  return ()

class KripkeLike a where
  getNodes :: a -> [(String,String)] -- nid,nlabel
  getEdges :: a -> [(String,String,String)] -- elabel,from,to
  getActuals :: a -> [String] -- nid
  getActuals = const []
  directed :: a -> Bool
  directed = const True
  nodeAts :: a -> Bool -> Attributes
  nodeAts _ True  = [shape DoubleCircle]
  nodeAts _ False = [shape Circle]
  toGraph :: a -> Data.GraphViz.Types.Generalised.DotGraph String
  toGraph x = (if directed x then digraph' else graph') $ do
    let nodes = getNodes x
    let actuals = filter (\n -> fst n `elem` getActuals x) nodes
    mapM_
      (\(nid,nlabel) -> node nid (toLabel nlabel : nodeAts x True))
      actuals
    mapM_
      (\(nid,nlabel) -> node nid (toLabel nlabel : nodeAts x False))
      (nodes \\ actuals)
    mapM_
      (\(elabel,from,to) -> edge from to [toLabel elabel])
      (getEdges x)
  dispDot :: a -> IO ()
  dispDot x = runGraphvizCanvas Dot (toGraph x) Xlib
  textDot :: a -> T.Text
  textDot = T.intercalate " " . T.lines . printDotGraph . toGraph
  svg :: a -> String
  svg x = unsafePerformIO $
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      _ <- runGraphvizCommand Dot (toGraph x) Svg (tmpdir ++ "/temp.svg")
      readFile (tmpdir ++ "/temp.svg")

newtype ViaDot a = ViaDot a
  deriving (Eq,Ord,Show)

instance (Ord a, Show a, KripkeLike a) => TexAble (ViaDot a) where
  tex (ViaDot x) = unsafePerformIO $
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      _ <- runGraphviz (toGraph x) DotOutput (tmpdir ++ "/temp.dot")
      runAndWait $ "dot2tex --figonly -ftikz -traw -p --autosize -w --usepdflatex "++tmpdir++"/temp.dot | sed '/^$/d' > "++tmpdir++"/temp.tex;"
      readFile (tmpdir ++ "/temp.tex")
  texTo (ViaDot x) filename = do
    _ <- runGraphviz (toGraph x) DotOutput (filename ++ ".dot")
    runAndWait $ "dot2tex --figonly -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot | sed '/^$/d' > "++filename++".tex;"
  texDocumentTo (ViaDot x) filename = do
    _ <- runGraphviz (toGraph x) DotOutput (filename ++ ".dot")
    runAndWait $ "dot2tex -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot -o "++filename++".tex;"
