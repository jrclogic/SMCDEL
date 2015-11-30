
module SMCDEL.Other.BDD2Form where
import Data.HasCacBDD
import Test.QuickCheck
import SMCDEL.Language hiding (Bot,Top)
import qualified SMCDEL.Language (Form(Bot,Top))
import SMCDEL.Symbolic.HasCacBDD

formOf :: Bdd -> Form
formOf b = formOfTree $ unravel b

formOfTree :: BddTree -> Form
formOfTree Bot = SMCDEL.Language.Bot
formOfTree Top = SMCDEL.Language.Top
formOfTree (Var n Top  Bot)   = PrpF (P n)
formOfTree (Var n Bot  Top)   = Neg $ PrpF (P n)
formOfTree (Var n Top  right) = Disj [ PrpF (P n), formOfTree right ]
formOfTree (Var n Bot  right) = Conj [ Neg $ PrpF (P n), formOfTree right ]
formOfTree (Var n left Top)   = Disj [ Neg $ PrpF (P n), formOfTree left ]
formOfTree (Var n left Bot)   = Conj [ PrpF (P n), formOfTree left ]
formOfTree (Var n left right) =
  Disj [ Conj [ PrpF (P n), formOfTree left ] ,
          Conj [ Neg $ PrpF (P n), formOfTree right ] ]

myTest :: IO Result
myTest = quickCheckResult ( \b -> b == boolBddOf (formOf b) )

myOtherTest :: IO Result
myOtherTest = quickCheckResult ( \(BF f) -> boolBddOf (Equi f (formOf (boolBddOf f)))  == top )
