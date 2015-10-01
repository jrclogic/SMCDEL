{
module Parse where
import Token
import DELLANG
}

%name parse CheckInput
%tokentype { Token }
%error { parseError }

%token
  VARS  { TokenVARS }
  LAW { TokenLAW }
  OBS { TokenOBS }
  VALIDQ { TokenVALIDQ }
  WHEREQ { TokenWHEREQ }
  COLON { TokenColon }
  COMMA { TokenComma }
  TOP { TokenTop }
  BOT { TokenBot }
  '(' { TokenOB }
  ')' { TokenCB }
  '[' { TokenCOB }
  ']' { TokenCCB }
  '<' { TokenLA }
  '>' { TokenRA }
  '!' { TokenExclam }
  '?' { TokenQuestm }
  '&' { TokenBinCon }
  '|' { TokenBinDis }
  '~' { TokenNeg }
  '->' { TokenImpl }
  CON { TokenCon }
  DIS { TokenDis }
  XOR { TokenXor }
  STR { TokenStr $$ }
  INT { TokenInt $$ }
  'iff' { TokenEqui }
  KNOWSTHAT { TokenInfixKnowThat }
  KNOWSWHETHER { TokenInfixKnowWhether }
  CKNOWTHAT { TokenInfixCKnowThat }
  CKNOWWHETHER { TokenInfixCKnowWhether }
  'Forall' { TokenForall }
  'Exists' { TokenExists }

%left '&'
%left '|'
%nonassoc '~'

%%

CheckInput : VARS IntList LAW Form OBS ObserveSpec JobList { CheckInput $2 $4 $6 $7 }
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
     | Form 'iff' Form { Equi $1 $3 }
     | INT { PrpF (P $1) }
     | String KNOWSTHAT Form { K $1 $3 }
     | String KNOWSWHETHER Form { Kw $1 $3 }
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
ObservLine : STR COLON IntList { ($1,$3) }
ObserveSpec : ObservLine { [$1] } | ObservLine ObserveSpec { $1:$2 }
JobList : JobLine { [$1] } | JobLine JobList { $1:$2 }
JobLine : VALIDQ Form { Left $2 } | WHEREQ Form { Right $2 }

{
data CheckInput = CheckInput [Int] Form [(String,[Int])] [Either Form Form] deriving (Show,Eq,Ord)
type IntList = [Int]
type FormList = [Form]
type ObserveLine = (String,IntList)
type ObserveSpec = [ObserveLine]

parseError :: [Token] -> a
parseError list = error ("Parse error on: " ++ show list)
}
