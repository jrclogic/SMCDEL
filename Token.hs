module Token where
data Token =
  TokenVARS | TokenLAW | TokenOBS | TokenVALIDQ | TokenWHEREQ | TokenColon | TokenComma |
  TokenStr String | TokenInt Int | TokenTop | TokenBot | TokenPrp | TokenNeg |
  TokenOB | TokenCB | TokenCOB | TokenCCB | TokenLA | TokenRA | TokenExclam | TokenQuestm |
  TokenBinCon | TokenBinDis | TokenCon | TokenDis | TokenXor | TokenImpl | TokenEqui |
  TokenForall | TokenExists | TokenInfixKnowWhether | TokenInfixKnowThat |
  TokenInfixCKnowWhether | TokenInfixCKnowThat
  deriving (Eq,Show)
