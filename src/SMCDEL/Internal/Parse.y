{
{-# OPTIONS_GHC -w #-}
module SMCDEL.Internal.Parse where
import SMCDEL.Internal.Token
import SMCDEL.Internal.Lex
import SMCDEL.Language
}

%name parseCheckInput CheckInput
%name parseForm Form
%name parseFormList FormList

%tokentype { Token AlexPosn }
%error { parseError }

%monad { ParseResult } { >>= } { Right }

%token
  VARS   { TokenVARS   _ }
  LAW    { TokenLAW    _ }
  OBS    { TokenOBS    _ }
  TRUEQ  { TokenTRUEQ  _ }
  VALIDQ { TokenVALIDQ _ }
  WHEREQ { TokenWHEREQ _ }
  COLON  { TokenColon  _ }
  COMMA  { TokenComma  _ }
  TOP    { TokenTop    _ }
  BOT    { TokenBot    _ }
  '('    { TokenOB     _ }
  ')'    { TokenCB     _ }
  '['    { TokenCOB    _ }
  ']'    { TokenCCB    _ }
  '{'    { TokenSOB    _ }
  '}'    { TokenSCB    _ }
  '<'    { TokenLA     _ }
  '>'    { TokenRA     _ }
  '!'    { TokenExclam _ }
  '?'    { TokenQuestm _ }
  '&'    { TokenBinCon _ }
  '|'    { TokenBinDis _ }
  '~'    { TokenNeg    _ }
  '->'   { TokenImpl   _ }
  CON    { TokenCon    _ }
  DIS    { TokenDis    _ }
  XOR    { TokenXor    _ }
  ONEOF  { TokenOneOf  _ }
  STR    { TokenStr $$ _ }
  INT    { TokenInt $$ _ }
  'iff'  { TokenEqui   _ }
  K      { TokenPrefixK _ }
  Kw     { TokenPrefixKw _ }
  KNOWSTHAT    { TokenInfixKnowThat     _ }
  KNOWSWHETHER { TokenInfixKnowWhether  _ }
  CKNOWTHAT    { TokenInfixCKnowThat    _ }
  CKNOWWHETHER { TokenInfixCKnowWhether _ }
  'Forall'     { TokenForall            _ }
  'Exists'     { TokenExists            _ }

%left '->' 'iff'
%left '|' '&'
%nonassoc '&' '|'
%left KNOWSTHAT KNOWSWHETHER CKNOWTHAT CKNOWWHETHER
%left '[' ']'
%left '<' '>'
%left '~'

%%

CheckInput : VARS IntList LAW Form OBS ObserveSpec JobList { CheckInput $2 $4 $6 $7 }
           | VARS IntList LAW Form OBS ObserveSpec { CheckInput $2 $4 $6 [] }
IntList : INT { [$1] }
        | INT COMMA IntList { $1:$3 }
Form : TOP { Top }
     | BOT { Bot }
     | '(' Form ')' { $2 }
     | '~' Form { Neg $2 }
     | CON '(' FormList ')' { Conj $3 }
     | Form '&' Form { Conj [$1,$3] }
     | Form '|' Form { Disj [$1,$3] }
     | Form '->' Form { Impl $1 $3 }
     | DIS '(' FormList ')' { Disj $3 }
     | XOR '(' FormList ')' { Xor $3 }
     | ONEOF '(' FormList ')' { oneOf $3 }
     | Form 'iff' Form { Equi $1 $3 }
     | INT { PrpF (P $1) }
     | K String Form { K $2 $3 }
     | Kw String Form { Kw $2 $3 }
     | String KNOWSTHAT Form { K $1 $3 }
     | String KNOWSWHETHER Form { Kw $1 $3 }
     | String KNOWSWHETHER '(' FormList ')' { Conj (map (Kw $1) $4) }
     | StringList CKNOWTHAT Form { Ck $1 $3 }
     | StringList CKNOWWHETHER Form { Ckw $1 $3 }
     | '(' StringList ')' CKNOWTHAT Form { Ck $2 $5 }
     | '(' StringList ')' CKNOWWHETHER Form { Ckw $2 $5 }
     | '[' '!' Form ']'     Form { PubAnnounce  $3 $5 }
     | '[' '?' '!' Form ']' Form { PubAnnounceW $4 $6 }
     | '<' '!' Form '>'     Form { Neg (PubAnnounce  $3 (Neg $5)) }
     | '<' '?' '!' Form '>' Form { Neg (PubAnnounceW $4 (Neg $6)) }
     -- announcements to a group:
     | '[' StringList '!' Form ']'     Form { Announce $2 $4 $6 }
     | '[' StringList '?' '!' Form ']' Form { AnnounceW $2 $5 $7 }
     | '<' StringList '!' Form '>'     Form { Neg (Announce  $2 $4 (Neg $6)) }
     | '<' StringList '?' '!' Form '>' Form { Neg (AnnounceW $2 $5 (Neg $7)) }
     -- boolean quantifiers:
     | 'Forall' IntList Form { Forall (map P $2) $3 }
     | 'Exists' IntList Form { Exists (map P $2) $3 }
FormList : Form { [$1] } | Form COMMA FormList { $1:$3 }
String : STR { $1 }
StringList : String { [$1] } | String COMMA StringList { $1:$3 }
ObserveLine : STR COLON IntList { ($1,$3) }
ObserveSpec : ObserveLine { [$1] } | ObserveLine ObserveSpec { $1:$2 }
JobList : Job { [$1] } | Job JobList { $1:$2 }
State : '{' '}' { [] }
      | '{' IntList '}' { $2 }
Job : TRUEQ State Form { TrueQ $2 $3 }
    | VALIDQ Form { ValidQ $2 }
    | WHEREQ Form { WhereQ $2 }

{
data CheckInput = CheckInput [Int] Form [(String,[Int])] JobList deriving (Show,Eq,Ord)
data Job = TrueQ IntList Form | ValidQ Form | WhereQ Form deriving (Show,Eq,Ord)
type JobList = [Job]
type IntList = [Int]
type FormList = [Form]
type ObserveLine = (String,IntList)
type ObserveSpec = [ObserveLine]

type ParseResult a = Either (Int,Int) a

parseError :: [Token AlexPosn] -> ParseResult a
parseError []     = Left (1,1)
parseError (t:ts) = Left (lin,col)
  where (AlexPn abs lin col) = apn t

class Parse a where
  parse :: [Token AlexPosn] -> Either (Int,Int) a
  parseS :: String -> Either (Int,Int) a
  parseS input =
    case alexScanTokensSafe input of
      Left pos -> Left pos
      Right lexResult -> case parse lexResult of
        Left pos -> Left pos
        Right x -> Right x
  unsafeParseS :: String -> a
  unsafeParseS input =
    case alexScanTokensSafe input of
      Left pos -> error $ "Lex error at " ++ show pos
      Right lexResult -> case parse lexResult of
        Left pos -> error $ "Parse error at " ++ show pos
        Right x -> x

instance Parse CheckInput where
  parse = parseCheckInput

instance Parse Form where
  parse = parseForm

instance Parse FormList where
  parse = parseFormList
}
