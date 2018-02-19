module SMCDEL.Other.BDD2Form where
import Data.HasCacBDD
import SMCDEL.Language hiding (Bot,Top)
import qualified SMCDEL.Language (Form(Bot,Top))

formOf :: Bdd -> Form
formOf = simplify . formOfTree . unravel

formOfTree :: BddTree -> Form
formOfTree Bot                = SMCDEL.Language.Bot
formOfTree Top                = SMCDEL.Language.Top
formOfTree (Var n Top  Bot)   = PrpF (P n)
formOfTree (Var n Bot  Top)   = Neg $ PrpF (P n)
formOfTree (Var n Top  right) = Disj [ PrpF (P n), formOfTree right ]
formOfTree (Var n Bot  right) = Conj [ Neg $ PrpF (P n), formOfTree right ]
formOfTree (Var n left Top)   = Disj [ Neg $ PrpF (P n), formOfTree left ]
formOfTree (Var n left Bot)   = Conj [ PrpF (P n), formOfTree left ]
formOfTree (Var n left right) =
  Disj [ Conj [ PrpF (P n), formOfTree left ] ,
          Conj [ Neg $ PrpF (P n), formOfTree right ] ]
