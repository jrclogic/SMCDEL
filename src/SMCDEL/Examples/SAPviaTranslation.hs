
module Main where
import Data.List
import DELLANG
import KRIPKEDEL
import SYMDEL
import KNSCAC

-- the upper bound
upb :: Int
upb = 100

--possible pairs 1<x<y, x+y<=100
pairs :: [(Int, Int)]
pairs = [(x,y) | x<-[2..100], y<-[2..100], x<y, x+y<=upb]

ipairs :: [(State, (Int, Int))]
ipairs = zip [0..] pairs

-- We only have one set of variables in SMCDEL, so we encode
-- "x is n" and "y is m" as $P_n$ and $P_{100+m}$ respectively.
xPrp, yPrp :: Int -> Prp
xPrp = P
yPrp n = P (100 + n)

xIs, yIs :: Int -> Form
xIs n = PrpF $ xPrp n
yIs n = PrpF $ yPrp n

xProps, yProps :: [Prp]
xProps = map xPrp [2..100]
yProps = map yPrp [2..100]

-- initial Kripke model
sapKripke :: KripkeModel
sapKripke = KrM (map fst ipairs) rel val where
  val   = [(w, [(p,xPrp x == p) | p<-xProps] ++ [(q,yPrp y == q) | q<-yProps] ) | (w,(x,y))<- ipairs ]
  rel   = [ (alice,partWith (+)) , (bob,partWith (*)) ]
  partWith op = map (map fst) $ groupBy (\(_,(x,y)) (_,(x',y')) -> op x y == op x' y') $
    sortBy (\(_,(x,y)) (_,(x',y')) -> compare (op x y) (op x' y')) ipairs

-- convert it to a knowledge structure, ignoring the actual world
sapKnStruct :: KnowStruct
sapKnStruct = fst $ kripkeToKns (sapKripke,0)

fmrs1e, fmrp2e, fmrs3e :: Form

--Sum says: I knew that you didn't know the two numbers.
fmrs1e = K alice $ Conj [ Disj [ Neg (Conj [xIs x,yIs y])
                               , Neg (K bob (Conj [xIs x,yIs y])) ] | (x,y)<-pairs ]

--Product says: Now I know the two numbers
fmrp2e = Conj [ Disj [ Neg (Conj [xIs x,yIs y])
                     , K bob (Conj [xIs x,yIs y]) ] | (x,y)<-pairs ]

--Sum says: Now I know the two numbers too
fmrs3e = Conj [ Disj [ Neg (Conj [xIs x,yIs y])
                     , K alice (Conj [xIs x,yIs y]) ] | (x,y)<-pairs ]

protocol :: Form
protocol = Conj [ fmrs1e
                , PubAnnounce fmrs1e fmrp2e
                , PubAnnounce fmrs1e (PubAnnounce fmrp2e fmrs3e) ]

main :: IO ()
main = do
  -- finding the solution
  putStr "States where the announcements are truthful: "
  print $ statesOf (KNSCAC.pubAnnounce sapKnStruct protocol)

  -- verifying that it is a solution
  putStr "If x==4 and y==13, then the announcements are truthful: "
  print $ validViaBdd sapKnStruct (Impl (Conj [xIs 4, yIs 13]) protocol)

  -- verifying that it is the unique solution
  putStr "If the announcements are truthful, then x==4 and y==13: "
  print $ validViaBdd sapKnStruct (Impl protocol (Conj [xIs 4, yIs 13]))
