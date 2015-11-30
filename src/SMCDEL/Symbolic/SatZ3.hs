
module SMCDEL.Symbolic.SatZ3 where

import Z3.Monad hiding (eval)
import Data.List
import SMCDEL.Language
import SMCDEL.Internal.Help (apply)
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (foldM,join)

prp2var :: Prp -> Z3 AST
prp2var (P n) = mkStringSymbol (show n) >>= mkBoolVar

ps2apps :: [Prp] -> Z3 [App]
ps2apps ps = mapM toApp =<< mapM prp2var ps

boolAstOf :: Form -> Z3 AST
boolAstOf Top           = mkTrue
boolAstOf Bot           = mkFalse
boolAstOf (PrpF p)      = prp2var p
boolAstOf (Neg forms)   = boolAstOf forms >>= mkNot
boolAstOf (Conj forms)  = mapM boolAstOf forms >>= mkAnd
boolAstOf (Disj forms)  = mapM boolAstOf forms >>= mkOr
boolAstOf (Impl f1 f2)  = join $ mkImplies <$> boolAstOf f1 <*> boolAstOf f2
boolAstOf (Equi f1 f2)  = join $ mkIff     <$> boolAstOf f1 <*> boolAstOf f2
boolAstOf (Forall ps f) = join $ mkForallConst [] <$> ps2apps ps <*> boolAstOf f
boolAstOf (Exists ps f) = join $ mkExistsConst [] <$> ps2apps ps <*> boolAstOf f
boolAstOf f = error $ "boolAstOf failed: Usupported kind of formula:" ++ show f

satZ3 :: [AST] -> Z3 Bool
satZ3 asts = do
  mapM_ assert asts
  result <- solverCheck
  case result of
    Sat -> return True
    Unsat -> return False
    Undef -> error "boolEval failed: Z3 returned undefined!"

boolEval :: [Prp] -> Form -> IO Bool
boolEval truths form = evalZ3 $ do
  let allps = sort $ nub (truths ++ propsInForm form)
  tAsts  <- mapM prp2var truths
  fAsts  <- mapM prp2var (allps \\ truths)
  nfAsts <- mapM mkNot fAsts
  valAst <- mkAnd (tAsts++nfAsts)
  fAst <- boolAstOf form
  satZ3 [valAst,fAst]

-- | Instead of a BDD we represent the state law with a list of clauses
data KnowStruct = KnS [Prp] (Z3 AST) [(Agent,[Prp])] -- deriving (Show)
type KnState = [Prp]
type Scenario = (KnowStruct, KnState)

mkListXor :: [AST] -> Z3 AST
mkListXor [] = mkFalse
mkListXor (b:bs) = foldM mkXor b bs

-- | Translate a DEL formula to a boolean Z3 AST
astOf :: KnowStruct -> Form -> Z3 AST
astOf _   Top           = mkTrue
astOf _   Bot           = mkFalse
astOf _   (PrpF p)      = prp2var p
astOf kns (Neg forms)   = astOf kns forms >>= mkNot
astOf kns (Conj forms)  = mapM (astOf kns) forms >>= mkAnd
astOf kns (Disj forms)  = mapM (astOf kns) forms >>= mkOr
astOf kns (Xor forms)   = mapM (astOf kns) forms >>= mkListXor
astOf kns (Impl f1 f2)  = join $ mkImplies <$> astOf kns f1 <*> astOf kns f2
astOf kns (Equi f1 f2)  = join $ mkIff     <$> astOf kns f1 <*> astOf kns f2
astOf kns (Forall ps f) = join $ mkForallConst [] <$> ps2apps ps <*> astOf kns f
astOf kns (Exists ps f) = join $ mkExistsConst [] <$> ps2apps ps <*> astOf kns f
astOf kns@(KnS allps lawZ3 obs) (K i form) = do
  otherpsApps <- ps2apps (allps \\ apply obs i)
  fAst <- astOf kns form
  lawAst <- lawZ3
  implAst <- mkImplies lawAst fAst
  mkForallConst [] otherpsApps implAst
astOf kns@(KnS allps lawZ3 obs) (Kw i form) = do
  otherpsApps <- ps2apps (allps \\ apply obs i)
  fAst <- astOf kns form
  nfAst <- astOf kns (Neg form)
  lawAst <- lawZ3
  implAst1 <- mkImplies lawAst fAst
  implAst2 <- mkImplies lawAst nfAst
  a1 <- mkForallConst [] otherpsApps implAst1
  a2 <- mkForallConst [] otherpsApps implAst2
  mkOr [a1,a2]
astOf kns (PubAnnounce form1 form2) = astOf (pubAnnounce kns form1) form2
astOf kns (PubAnnounceW form1 form2) = do
  fif <- astOf kns form1
  fthen <- astOf (pubAnnounce kns form1) form2
  felse <- astOf (pubAnnounce kns (Neg form1)) form2
  mkIte fif fthen felse
astOf _   f = error $ "astOf failed: Unsupported kind of formula: " ++ show f

-- | Evaluate formula on a Scenario
evalViaZ3 :: Scenario -> Form -> Bool
evalViaZ3 (kns@(KnS allps lawZ3 _),s) f = unsafePerformIO $ evalZ3 $ do
  -- valuation
  tAsts  <- mapM prp2var s
  fAsts  <- mapM prp2var (allps \\ s)
  nfAsts <- mapM mkNot fAsts
  valAst <- mkAnd (tAsts++nfAsts)
  -- law
  lawAst <- lawZ3
  -- formula
  fAst <- astOf kns f
  satZ3 [valAst,lawAst,fAst]

-- | Check whether a formula is valid on a Knowledge Structure by
-- checking if its negation is not satisfiable with the state law.
validViaZ3 :: KnowStruct -> Form -> Bool
validViaZ3 kns@(KnS _ lawZ3 _) form = unsafePerformIO $ evalZ3 $ do
  lawAst <- lawZ3
  nfAst  <- astOf kns (Neg form)
  fmap not (satZ3 [lawAst,nfAst])

-- | Announcing: Add the boolean equivalent clause to the law AST.
pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawZ3 obs) psi = KnS props newlawZ3 obs where
  newlawZ3 = do
    annAst <- astOf kns psi
    oldlawAst <- lawZ3
    mkAnd [oldlawAst,annAst]

-- | Truthful announcement on Scenarios.
pubAnnounceOnScn :: Scenario -> Form -> Scenario
pubAnnounceOnScn (kns,s) psi =
  if evalViaZ3 (kns,s) psi
    then (pubAnnounce kns psi,s)
    else error "pubAnnounceOnScn Liar!"
