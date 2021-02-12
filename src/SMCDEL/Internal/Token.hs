module SMCDEL.Internal.Token where
data Token a -- == AlexPn
  = TokenVARS              {apn :: a}
  | TokenLAW               {apn :: a}
  | TokenOBS               {apn :: a}
  | TokenTRUEQ            {apn :: a}
  | TokenVALIDQ            {apn :: a}
  | TokenWHEREQ            {apn :: a}
  | TokenColon             {apn :: a}
  | TokenComma             {apn :: a}
  | TokenStr {fooS::String, apn :: a}
  | TokenInt {fooI::Int,    apn :: a}
  | TokenTop               {apn :: a}
  | TokenBot               {apn :: a}
  | TokenPrp               {apn :: a}
  | TokenNeg               {apn :: a}
  | TokenOB                {apn :: a}
  | TokenCB                {apn :: a}
  | TokenCOB               {apn :: a}
  | TokenCCB               {apn :: a}
  | TokenSOB               {apn :: a}
  | TokenSCB               {apn :: a}
  | TokenLA                {apn :: a}
  | TokenRA                {apn :: a}
  | TokenExclam            {apn :: a}
  | TokenQuestm            {apn :: a}
  | TokenBinCon            {apn :: a}
  | TokenBinDis            {apn :: a}
  | TokenCon               {apn :: a}
  | TokenDis               {apn :: a}
  | TokenXor               {apn :: a}
  | TokenImpl              {apn :: a}
  | TokenEqui              {apn :: a}
  | TokenForall            {apn :: a}
  | TokenExists            {apn :: a}
  | TokenInfixKnowWhether  {apn :: a}
  | TokenInfixKnowThat     {apn :: a}
  | TokenInfixCKnowWhether {apn :: a}
  | TokenInfixCKnowThat    {apn :: a}
  deriving (Eq,Show)
