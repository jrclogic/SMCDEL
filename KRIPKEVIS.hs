module KRIPKEVIS where
import Data.List
import Data.Maybe (fromJust)
import System.IO
import System.Process

begintab, endtab, newline :: String
begintab  = "\\\\begin{tabular}{c}"
endtab    = "\\\\end{tabular}"
newline   = " \\\\\\\\[0pt] "

type PartitionOf a = [[a]]

data VisModel a b c = VisModel [a] [(b,PartitionOf a)] [(a,c)] a

type Rel a = [(a,a)]
data GenVisModel a b c = GenVisModel [a] [(b,Rel a)] [(a,c)] a

stringModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> String
stringModel showState showAgents showVal information model =
  "graph G { \n"
    ++ "  node [shape=doublecircle,label=\""
    ++ labelof cur ++ "\"] w" ++ showState cur ++ ";\n"
    ++ concat [ ndlinefor s | s <- otherstates ]
    ++ "  rankdir=LR; \n size=\"6,5!\" \n"
    ++ concat [ "  w" ++ show x ++" -- w"++ show y
              ++"[ label = \""++ showAgents a ++"\" ]; \n"
            | (a,x,y) <- edges  ]
    ++ "  label = \""++information++"\"; \n "
    ++ "} \n"
  where
    (VisModel states rel val cur) = model
    labelof s = begintab ++ "\\\\textbf{" ++ showState s ++ "}" ++ newline ++ showVal (fromJust $ lookup s val) ++ endtab
    ndlinefor s = "  node [shape=circle,label=\""
                ++ labelof s ++ "\"] w" ++ show s ++ ";\n"
    otherstates = delete cur states
    edges = nub $ concat $ concat $ concat [ [ [ [(a,x,y) | x<y] | x <- part, y <- part ] | part <- fromJust $ lookup a rel ] | a <- map fst rel ]

stringGenModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> GenVisModel a b c
      -> String
stringGenModel showState showAgents showVal information (GenVisModel states rel val cur) =
  "digraph G { \n"
    ++ "  node [shape=doublecircle,label=\""
    ++ labelof cur ++ "\"] w" ++ showState cur ++ ";\n"
    ++ concat [ ndlinefor s | s <- otherstates ]
    ++ "  rankdir=LR; \n size=\"6,5!\" \n"
    ++ concat [ "  w" ++ show x ++" -- w"++ show y
              ++"[ label = \""++ showAgents a ++"\" ]; \n"
            | (a,x,y) <- edges  ]
    ++ "  label = \""++information++"\"; \n "
    ++ "} \n"
  where
    labelof s = begintab ++ "\\\\textbf{" ++ showState s ++ "}" ++ newline ++ showVal (fromJust $ lookup s val) ++ endtab
    ndlinefor s = "  node [shape=circle,label=\""
                ++ labelof s ++ "\"] w" ++ show s ++ ";\n"
    otherstates = delete cur states
    edges = concat [ [ (a,x,y) | (x,y) <- fromJust $ lookup a rel ] | a <- map fst rel ]

dotModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> String -> IO String
dotModel showState showAgents showVal info model filename =
  let gstring = stringModel showState showAgents showVal info model
  in do
    newFile <- openFile filename WriteMode
    hPutStrLn newFile gstring
    hClose newFile
    return ("Model was DOT'd to "++filename)

dotGenModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> GenVisModel a b c
      -> String -> IO String
dotGenModel showState showAgents showVal info model filename =
  let gstring = stringGenModel showState showAgents showVal info model
  in do
    newFile <- openFile filename WriteMode
    hPutStrLn newFile gstring
    hClose newFile
    return ("Model was DOT'd to "++filename)

texModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> String -> IO String
texModel showState showAgents showVal info model filename =
  do
    forget <- dotModel showState showAgents showVal info model ("tmp/"++filename++".dot")
    putStrLn forget
    _ <- system ("cd tmp/; dot2tex --figonly -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot > "++filename++".tex;" )
    return ("Model was TeX'd to tmp/" ++ filename ++ ".tex")

texGenModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> GenVisModel a b c
      -> String -> IO String
texGenModel showState showAgents showVal info model filename =
  do
    forget <- dotGenModel showState showAgents showVal info model ("tmp/"++filename++".dot")
    putStrLn forget
    _ <- system ("cd tmp/; dot2tex --figonly -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot > "++filename++".tex;" )
    return ("Model was TeX'd to tmp/" ++ filename ++ ".tex")

pdfModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> String -> IO String
pdfModel showState showAgents showVal info model filename =
  do
    forget <- dotModel showState showAgents showVal info model ("tmp/"++filename++".dot")
    putStrLn forget
    _ <- system ("cd tmp/; dot2tex -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot > "++filename++".tex; pdflatex -interaction=nonstopmode "++filename++".tex > "++filename++".pdflatex.log;" )
    return ("Model was PDF'd to tmp/" ++ filename ++ ".pdf")

svgModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> String -> IO String
svgModel showState showAgents showVal info model filename =
  do
    forget <- dotModel showState showAgents showVal info model ("tmp/"++filename++".dot")
    putStrLn forget
    _ <- system ("cd tmp/; dot2tex -ftikz -traw -p --autosize -w --usepdflatex "++filename++".dot > "++filename++".tex; pdflatex -interaction=nonstopmode "++filename++".tex > temp.pdflatex.log; pdftocairo -svg "++filename++".pdf "++filename++".svg" )
    return ("Model was SVG'd to tmp/" ++ filename ++ ".pdf")

dispModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> VisModel a b c
      -> IO ()
dispModel showState showAgents showVal info model =
  do
    forget <- dotModel showState showAgents showVal info model "tmp/temp.dot"
    putStrLn forget
    _ <- system "cd tmp/; dot2tex -ftikz -traw -p --autosize -w --usepdflatex temp.dot > temp.tex; pdflatex -interaction=nonstopmode temp.tex > temp.pdflatex.log; okular temp.pdf 2>&1 | cat > temp.okular.log;"
    putStrLn "Model was TeX'd and shown."
    return ()

dispGenModel :: Ord a => Eq a => Eq b => Show a => Show b =>
  (a -> String) -> (b -> String) -> (c -> String) -> String
    -> GenVisModel a b c
      -> IO ()
dispGenModel showState showAgents showVal info model =
  do
    forget <- dotGenModel showState showAgents showVal info model "tmp/temp.dot"
    putStrLn forget
    _ <- system "cd tmp/; dot2tex -ftikz -traw -p --autosize -w --usepdflatex temp.dot > temp.tex; pdflatex -interaction=nonstopmode temp.tex > temp.pdflatex.log; okular temp.pdf 2>&1 | cat > temp.okular.log;"
    putStrLn "Model was TeX'd and shown."
    return ()
