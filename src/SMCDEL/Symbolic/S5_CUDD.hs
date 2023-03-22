{-# LANGUAGE DerivingStrategies, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, PolyKinds, ScopedTypeVariables #-}

module SMCDEL.Symbolic.S5_CUDD where

import Cudd.Cudd (DdManager)
import Data.Char (isSpace)
import Data.GraphViz
import Data.GraphViz.Printing (renderDot)
import qualified Data.GraphViz.Types.Generalised as DotGen
import Data.List ((\\), dropWhileEnd, intercalate)
import qualified Data.Text.Lazy as B
import Data.Typeable()
import System.IO
import System.IO.Temp
import System.IO.Unsafe (unsafePerformIO)
import System.Process ( runInteractiveCommand )

import SMCDEL.Internal.Help (apply,powerset)
import SMCDEL.Internal.MyHaskCUDD
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language

-- | Knowledge structures using a BDD or ZDD variant.
data KnowStruct a b c =
  KnS Cudd.Cudd.DdManager [Prp] (Dd a b c) [(Agent,[Prp])]
  deriving stock (Eq,Show)
type KnState = [Prp]
type KnowScene a b c = (KnowStruct a b c, KnState)

instance HasAgents (KnowStruct a b c) where
  agentsOf (KnS _ _ _ obs)= map fst obs

instance HasVocab (KnowStruct a b c) where
  vocabOf (KnS _ props _ _) = props

instance Pointed (KnowStruct a b c) KnState

-- DD Construction from Logic formulas

boolDdOf :: (DdCtx a b c) => Cudd.Cudd.DdManager -> Form -> Dd a b c
boolDdOf mgr Top           = top mgr
boolDdOf mgr Bot           = bot mgr
boolDdOf mgr (PrpF (P n))  = var mgr n
boolDdOf mgr (Neg form)    = neg mgr $ boolDdOf mgr form
boolDdOf mgr (Conj forms)  = conSet mgr $ map (boolDdOf mgr) forms
boolDdOf mgr (Disj forms)  = disSet mgr $ map (boolDdOf mgr) forms
boolDdOf mgr (Xor forms)   = xorSet mgr $ map (boolDdOf mgr) forms
boolDdOf mgr (Impl f g)    = imp mgr (boolDdOf mgr f) (boolDdOf mgr g)
boolDdOf mgr (Equi f g)    = equ mgr (boolDdOf mgr f) (boolDdOf mgr g)
boolDdOf mgr (Forall ps f) = boolDdOf mgr (foldl singleForall f ps) where
  singleForall g p = Conj [ substit p Top g, substit p Bot g ]
boolDdOf mgr (Exists ps f) = boolDdOf mgr (foldl singleExists f ps) where
  singleExists g p = Disj [ substit p Top g, substit p Bot g ]
boolDdOf _   f             = error $ "boolDdOf failed: Not a boolean formula:" ++ show f

ddOf :: (DdCtx a b c) => KnowStruct a b c -> Form -> Dd a b c
ddOf     (KnS mgr _ _ _) Top           = top mgr
ddOf     (KnS mgr _ _ _) Bot           = bot mgr
ddOf     (KnS mgr _ _ _) (PrpF (P n))  = var mgr n
ddOf kns@(KnS mgr _ _ _) (Neg form)    = neg mgr $ ddOf kns form
ddOf kns@(KnS mgr _ _ _) (Conj forms)  = conSet mgr $ map (ddOf kns) forms
ddOf kns@(KnS mgr _ _ _) (Disj forms)  = disSet mgr $ map (ddOf kns) forms
ddOf kns@(KnS mgr _ _ _) (Xor  forms)  = xorSet mgr $ map (ddOf kns) forms
ddOf kns@(KnS mgr _ _ _) (Impl f g)    = imp mgr (ddOf kns f) (ddOf kns g)
ddOf kns@(KnS mgr _ _ _) (Equi f g)    = equ mgr (ddOf kns f) (ddOf kns g)
ddOf kns@(KnS mgr _ _ _) (Forall ps f) = forallSet mgr (map fromEnum ps) (ddOf kns f)
ddOf kns@(KnS mgr _ _ _) (Exists ps f) = existsSet mgr (map fromEnum ps) (ddOf kns f)
ddOf kns@(KnS mgr allprops lawbdd obs) (K i form) =
  forallSet mgr otherps (imp mgr lawbdd (ddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i --what does this do?
ddOf kns@(KnS mgr allprops lawbdd obs) (Kw i form) =
  disSet mgr [ forallSet mgr otherps (imp mgr lawbdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
ddOf kns@(KnS mgr allprops lawbdd obs) (Ck ags form) = gfp mgr lambda where
  lambda z = conSet mgr $ ddOf kns form : [ forallSet mgr (otherps i) (imp mgr lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
ddOf kns@(KnS mgr _ _ _) (Ckw ags form) = dis mgr (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))
ddOf kns@(KnS mgr props _ _) (Announce ags form1 form2) =
  imp mgr (ddOf kns form1) (restrict mgr bdd2 (k,True)) where
    bdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props
ddOf kns@(KnS mgr props _ _) (AnnounceW ags form1 form2) =
  ifthenelse mgr (ddOf kns form1) bdd2a bdd2b where
    bdd2a = restrict mgr (ddOf (announce kns ags form1) form2) (k,True)
    bdd2b = restrict mgr (ddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
ddOf kns@(KnS mgr _ _ _) (PubAnnounce form1 form2) = imp mgr (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2
ddOf kns@(KnS mgr _ _ _) (PubAnnounceW form1 form2) =
  ifthenelse mgr (ddOf kns form1) newform2a newform2b where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2
ddOf _ (Dia _ _) = error "Dynamic operators are not implemented in S5_CUDD."

pubAnnounce :: (DdCtx a b c) => KnowStruct a b c -> Form -> KnowStruct a b c
pubAnnounce kns@(KnS mgr props lawbdd obs) psi = KnS mgr props newlawbdd obs where
  newlawbdd = con mgr lawbdd (ddOf kns psi)

announce :: (DdCtx a b c) => KnowStruct a b c -> [Agent] -> Form -> KnowStruct a b c
announce kns@(KnS mgr props lawbdd obs) ags psi = KnS mgr newprops newlawbdd newobs where
  proppsi@(P k) = freshp props
  newprops  = proppsi:props
  newlawbdd = con mgr lawbdd (equ mgr (var mgr k) (ddOf kns psi))
  newobs    = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]

evalAssDD :: (DdCtx a b c) => Cudd.Cudd.DdManager -> Dd a b c -> (Int -> Bool) -> Bool
evalAssDD mgr (dd :: Dd a b c) f = bool where
  bool | b==(top mgr :: Dd a b c) = True
       | b==(bot mgr :: Dd a b c) = False
       | otherwise = error "evalAssBDD failed: DD leftover:\n"
  b    = restrictSet mgr dd list
  list = [ (n, f n) | n <- getSupport mgr dd ]

ddEval :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> Dd a b c -> Bool
ddEval mgr truths querybdd = evalAssDD mgr querybdd (\n -> P n `elem` truths)

whereViaDd :: DdCtx a b c => KnowStruct a b c -> Form -> [KnState]
whereViaDd kns f = statesOf (kns `update` f)

--Somewhat fast statesOf, faster woud be to use primitive construction of all Satifying Assignments (e.i. explicitly looping through the dd instead of using restrict).
statesOf :: DdCtx a b c => KnowStruct a b c -> [KnState]
statesOf (KnS mgr allprops lawdd _) = loop allprops lawdd where
  loop [] _ = []
  loop v d = r v d True ++ r v d False
  r ((P n):ns) d b
    | restrict mgr d (n,b) == bot mgr = []
    | restrict mgr d (n,b) == top mgr = if b then map ([P n] ++) (powerset ns) else powerset ns
    | otherwise =
      if b then map ([P n] ++) $ loop ns (restrict mgr d (n,b)) else loop ns (restrict mgr d (n,b))
  r [] _ _ = error "impossible?"

boolDDoutof :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> [Prp] -> Dd a b c
boolDDoutof mgr ps qs = conSet mgr $
  [ var mgr n | (P n) <- ps ] ++
  [ neg mgr $ var mgr n | (P n) <- qs \\ ps ]

ddToForm :: (DdCtx a b c) => Cudd.Cudd.DdManager -> [Prp] -> Dd a b c -> Form
ddToForm mgr v dd = unravel mgr dd (map P $ getDependentVars mgr (map fromEnum v) dd)

unravel :: (DdCtx a b c) => Cudd.Cudd.DdManager -> Dd a b c -> [Prp] -> Form
unravel _ _ [] = Top
unravel mgr dd [P n] = Disj [ result True, result False] where
  result True
    | restrict mgr dd (n, True) == bot mgr = Bot
    | otherwise = PrpF (P n)
  result False
    | restrict mgr dd (n, False) == bot mgr = Bot
    | otherwise  = Neg $ PrpF (P n)
unravel mgr dd (P n:ns) = Disj [ result True, result False] where
  result True
    | restrict mgr dd (n, True) == top mgr = PrpF (P n)
    | restrict mgr dd (n, True) == bot mgr = Bot
    | otherwise = Conj [PrpF (P n), unravel mgr (restrict mgr dd (n, True)) ns]
  result False
    | restrict mgr dd (n, False) == top mgr = Neg $ PrpF (P n)
    | restrict mgr dd (n, False) == bot mgr = Bot
    | otherwise = Conj [Neg $ PrpF (P n), unravel mgr (restrict mgr dd (n, False)) ns]

evalViaDd :: (DdCtx a b c) => KnowScene a b c -> Form -> Bool
evalViaDd ((kns@(KnS mgr allprops _ _),s) :: KnowScene a b c) f = bool where
  bool | b== (top mgr :: Dd a b c) = True
       | b== (bot mgr :: Dd a b c)  = False
       | otherwise = error ("evalViaDd failed: DD leftover:\n" ++ show b)
  b    = restrictSet mgr (ddOf kns f) list
  list = [ (n, P n `elem` s) | (P n) <- allprops ]

validViaDd :: (DdCtx a b c) => KnowStruct a b c -> Form -> Bool
validViaDd kns@(KnS mgr _ lawdd _) f = top mgr == imp mgr lawdd (ddOf kns f)

instance (DdCtx a b c) => Semantics (KnowScene a b c) where
  isTrue = evalViaDd

instance  (DdCtx a b c) => Semantics (KnowStruct a b c) where
  isTrue = validViaDd

instance (DdCtx a b c) => Update (KnowStruct a b c) Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate kns@(KnS mgr props lawdd obs) psi =
    KnS mgr props (con mgr lawdd (ddOf kns psi)) obs

-- * Visualisation functions

texDdWith :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> [Prp] -> String
texDdWith mgr d vocab = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  xDotText <- B.pack <$> returnDot mgr d
  -- currently uses P1 .. Pn for names of variables 1 .. n, can be changed when the parser accepts non number propositions
  let myShow = formatDotCUDD vocab
  let xDotGraph = parseDotGraphLiberally xDotText :: DotGen.DotGraph String
  let renamedXDotGraph = renameMyGraph xDotGraph myShow
  hPutStr i (B.unpack (renderDot $ toDot renamedXDotGraph) ++ "\n")
  handle <- openFile "xDotGraph.txt" ReadWriteMode
  hPrint handle (show xDotGraph ++ "\n\n" ++ show renamedXDotGraph)
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDdFun :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> (Int-> String) -> String
texDdFun mgr d myShowF = unsafePerformIO $ do
  (i,o,_,_) <- runInteractiveCommand "dot2tex --figpreamble=\"\\huge\" --figonly -traw"
  xDotText <- B.pack <$> returnDot mgr d
  let xDotGraph = (parseDotGraphLiberally xDotText :: DotGen.DotGraph String)
  let myShow = zip (map (\x -> " " ++ show x ++ " ") $ getSupport mgr d) (map myShowF $ getSupport mgr d)
  let renamedXDotGraph = renameMyGraph xDotGraph myShow
  hPutStr i (B.unpack (renderDot $ toDot renamedXDotGraph) ++ "\n")
  hClose i
  result <- hGetContents o
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

texDd :: DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> String
texDd mgr d = unsafePerformIO $ withSystemTempDirectory "smcdel" $ \tmpdir -> do
  writeToDot mgr d (tmpdir ++ "/texDd.dot")
  dot2tex $ dot2texDefaultArgs ++ " --figonly " ++ tmpdir ++ "/texDd.dot > " ++ tmpdir ++ "/texDd.tex;"
  result <- readFile (tmpdir ++ "/texDd.tex")
  return $ dropWhileEnd isSpace $ dropWhile isSpace result

data OwnedDd a b c = Owned Manager (Dd a b c)

instance DdCtx a b c => TexAble (OwnedDd a b c) where
  tex (Owned mgr dd) = texDd mgr dd

renameMyGraph :: DotGen.DotGraph String -> [(String, String)] -> DotGen.DotGraph String
renameMyGraph dg myShow =
  dg { DotGen.graphStatements = fmap changeGraphStatement (DotGen.graphStatements dg) } where
    changeGraphStatement gs = case gs of
      DotGen.SG sg -> DotGen.SG (sg {DotGen.subGraphStmts = fmap renameNodeNames (DotGen.subGraphStmts sg)}) where
        renameNodeNames sgStmt = case sgStmt of
          DotGen.DN dn -> DotGen.DN (renameNode dn myShow)
          DotGen.DE de -> DotGen.DE (renameEdge de myShow)
          x -> x
      DotGen.DE de -> DotGen.DE (renameEdge de myShow)
      x -> x

renameNode :: DotGen.DotNode String -> [(String, String)] -> DotGen.DotNode String
renameNode dn myShow = case lookup (DotGen.nodeID dn) myShow of
  (Just v) -> dn { nodeID = v } --nodeID is in myShow, thus replace the Int with the proposition
  Nothing -> dn --otherwise do nothing

renameEdge :: DotGen.DotEdge String -> [(String, String)] -> DotGen.DotEdge String
-- replace also the node name occurences in the edge statements
renameEdge de myShow = changeFromNode (changeToNode de) where
  changeToNode edge = case lookup (DotGen.toNode edge) myShow of
    (Just v) -> edge {toNode = v }
    Nothing -> edge
  changeFromNode edge = case lookup (DotGen.fromNode edge) myShow of
    (Just v) -> edge {fromNode = v }
    Nothing -> edge

formatDotCUDD :: [Prp] -> [(String, String)]
formatDotCUDD = map propToString where
  propToString p = (" " ++ show (fromEnum p - 1) ++ " ", "p" ++ show (fromEnum p))

instance DdCtx a b c => TexAble (KnowStruct a b c) where
  tex (KnS mgr props lawbdd obs) = concat
    [ " \\left( \n"
    , tex props ++ ", "
    , " \\begin{array}{l} \\scalebox{0.4}{"
    , texDd mgr lawbdd
    , "} \\end{array}\n "
    , ", \\begin{array}{l}\n"
    , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
    , "\\end{array}\n"
    , " \\right)" ]

instance DdCtx a b c => TexAble (KnowScene a b c) where
  tex (kns, state) = tex kns ++ " , " ++ tex state

giveDdTex ::  DdCtx a b c => Cudd.Cudd.DdManager -> Dd a b c -> String
giveDdTex mgr d = concat
  [
    " \\begin{array}{l} \\scalebox{0.4}{"
    , texDd mgr d
    , "} \\end{array}\n "]
