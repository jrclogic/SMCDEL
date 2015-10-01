{
module Lex where
import Token
}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-
  -- ignore whitespace and comments:
  $white+	;
  "--".*	;
  -- keywords and punctuation:
  "VARS"	{ \ _ s -> TokenVARS }
  "LAW"		{ \ _ s -> TokenLAW }
  "OBS"		{ \ _ s -> TokenOBS }
  "VALID?"	{ \ _ s -> TokenVALIDQ }
  "WHERE?"	{ \ _ s -> TokenWHEREQ }
  ":"		{ \ _ s -> TokenColon }
  ","		{ \ _ s -> TokenComma }
  "("		{ \ _ s -> TokenOB }
  ")"		{ \ _ s -> TokenCB }
  "["		{ \ _ s -> TokenCOB }
  "]"		{ \ _ s -> TokenCCB }
  "<"		{ \ _ s -> TokenLA }
  ">"		{ \ _ s -> TokenRA }
  "!"		{ \ _ s -> TokenExclam }
  "?"		{ \ _ s -> TokenQuestm }
  -- DEL Formulas:
  "Top"		{ \ _ s -> TokenTop }
  "Bot"		{ \ _ s -> TokenBot }
  "~"		{ \ _ s -> TokenNeg }
  "Not"		{ \ _ s -> TokenNeg }
  "not"		{ \ _ s -> TokenNeg }
  "&"		{ \ _ s -> TokenBinCon }
  "|"		{ \ _ s -> TokenBinDis }
  "->"		{ \ _ s -> TokenImpl }
  "iff"		{ \ _ s -> TokenEqui }
  "AND"		{ \ _ s -> TokenCon }
  "OR"		{ \ _ s -> TokenDis }
  "XOR"		{ \ _ s -> TokenXor }
  "ForAll"	{ \ _ s -> TokenForall }
  "Forall"	{ \ _ s -> TokenForall }
  "Exists"	{ \ _ s -> TokenExists }
  "knows whether" { \ _ s -> TokenInfixKnowWhether }
  "knows that" { \ _ s -> TokenInfixKnowThat }
  "comknow whether" { \ _ s -> TokenInfixCKnowWhether }
  "comknow that" { \ _ s -> TokenInfixCKnowThat }
  -- Integers and Strings:
  $digit+				{ \ _ s -> TokenInt (read s) }
  $alpha [$alpha $digit]*		{ \ _ s -> TokenStr s }
