{
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-missing-signatures #-}
module SMCDEL.Internal.Lex where
import SMCDEL.Internal.Token
}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  -- ignore whitespace and comments:
  $white+	;
  "--".*	;
  -- keywords and punctuation:
  "VARS"	{ \ p _ -> TokenVARS   p }
  "LAW"		{ \ p _ -> TokenLAW    p }
  "OBS"		{ \ p _ -> TokenOBS    p }
  "VALID?"	{ \ p _ -> TokenVALIDQ p }
  "WHERE?"	{ \ p _ -> TokenWHEREQ p }
  ":"		{ \ p _ -> TokenColon  p }
  ","		{ \ p _ -> TokenComma  p }
  "("		{ \ p _ -> TokenOB     p }
  ")"		{ \ p _ -> TokenCB     p }
  "["		{ \ p _ -> TokenCOB    p }
  "]"		{ \ p _ -> TokenCCB    p }
  "<"		{ \ p _ -> TokenLA     p }
  ">"		{ \ p _ -> TokenRA     p }
  "!"		{ \ p _ -> TokenExclam p }
  "?"		{ \ p _ -> TokenQuestm p }
  -- DEL Formulas:
  "Top"		{ \ p _ -> TokenTop    p }
  "Bot"		{ \ p _ -> TokenBot    p }
  "~"		{ \ p _ -> TokenNeg    p }
  "Not"		{ \ p _ -> TokenNeg    p }
  "not"		{ \ p _ -> TokenNeg    p }
  "&"		{ \ p _ -> TokenBinCon p }
  "|"		{ \ p _ -> TokenBinDis p }
  "->"		{ \ p _ -> TokenImpl   p }
  "iff"		{ \ p _ -> TokenEqui   p }
  "AND"		{ \ p _ -> TokenCon    p }
  "OR"		{ \ p _ -> TokenDis    p }
  "XOR"		{ \ p _ -> TokenXor    p }
  "ForAll"	{ \ p _ -> TokenForall p }
  "Forall"	{ \ p _ -> TokenForall p }
  "Exists"	{ \ p _ -> TokenExists p }
  "knows whether"   { \ p _ -> TokenInfixKnowWhether  p }
  "knows that"      { \ p _ -> TokenInfixKnowThat     p }
  "comknow whether" { \ p _ -> TokenInfixCKnowWhether p }
  "comknow that"    { \ p _ -> TokenInfixCKnowThat    p }
  -- Integers and Strings:
  $digit+				{ \ p s -> TokenInt (read s) p }
  $alpha [$alpha $digit]*		{ \ p s -> TokenStr s p }
