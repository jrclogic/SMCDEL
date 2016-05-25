{-# LANGUAGE FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, AllowAmbiguousTypes, OverloadedStrings #-}

module SMCDEL.Internal.TexDisplay where
import Data.List
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

type PartitionOf a = [[a]]

type Rel a = [(a,a)]

class (Eq a, Show a) => TexAble a where
  tex :: a -> String
  texTo :: a -> String -> IO ()
  texTo x filename = writeFile (filename++".tex") (tex x)
  texDocumentTo :: a -> String -> IO ()
  texDocumentTo x filename =
    writeFile (filename++".tex") (pre ++ tex x ++ post) where
      pre = "\\documentclass[a4paper,10pt]{article}\\usepackage[utf8]{inputenc}\\usepackage{tikz,fontenc,graphicx}\\usepackage[pdftex]{hyperref}\\hypersetup{pdfborder={0 0 0},breaklinks=true}\\begin{document}"
      post= "\\end{document}"
  pdfTo :: a -> String -> IO ()
  pdfTo x filename = do
    texDocumentTo x filename
    runAndWait $ "cd " ++ filename ++ "/../; /usr/bin/pdflatex -interaction=nonstopmode "++filename++".tex"
  disp :: a -> IO ()
  disp x = withSystemTempDirectory "smcdel" $ \tmpdir -> do
    pdfTo x (tmpdir ++ "/temp")
    runAndWait $ "/usr/bin/okular " ++ tmpdir ++ "/temp.pdf"

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
  (_,_,_,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  return ()

class KripkeLike a where
  getNodes :: a -> [(String,String)] -- nid,nlabel
  getEdges :: a -> [(String,String,String)] -- elabel,from,to
  getActuals :: a -> [String] -- nid
  getActuals = const []
  directed :: a -> Bool
  directed = const True
  toGraph :: a -> Data.GraphViz.Types.Generalised.DotGraph String
  toGraph x = (if directed x then digraph' else graph') $ do
    let nodes = getNodes x
    let actuals = filter (\n -> fst n `elem` getActuals x) nodes
    mapM_
      (\(nid,nlabel) -> node nid [shape DoubleCircle, toLabel $ nid ++":"++ nlabel])
      actuals
    mapM_
      (\(nid,nlabel) -> node nid [shape Circle, toLabel $ nid ++":"++ nlabel])
      (nodes \\ actuals)
    mapM_
      (\(elabel,from,to) -> edge from to [toLabel elabel])
      (getEdges x)
  dispDot :: a -> IO ()
  dispDot x = runGraphvizCanvas' (toGraph x) Xlib
  svg :: a -> String
  svg x = unsafePerformIO $
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      _ <- runGraphviz (toGraph x) Svg (tmpdir ++ "/temp.svg")
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
    _ <- runGraphviz (toGraph x) DotOutput filename
    runAndWait $ "dot2tex --figonly -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot | sed '/^$/d' > "++filename++".tex;"
  texDocumentTo (ViaDot x) filename = do
    _ <- runGraphviz (toGraph x) DotOutput filename
    runAndWait $ "dot2tex -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot -o "++filename++".tex;"
