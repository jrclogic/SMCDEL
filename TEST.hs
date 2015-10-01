
module TEST where
import System.Random (getStdRandom,randomR)
import DELLANG
import KNSCAC
import KRIPKEDEL
import SYMDEL
import EXAMPLES

mypropsindex, myagsindex, mycomplexity, myconlength :: Int
mypropsindex = 2 -- maximum index of atomic props
myagsindex   = 2 -- maximum index of agents
mycomplexity = 4 -- maximum complexity of formulas
myconlength  = 2 -- maximum number of conjuncts

getRandomInt :: Int -> IO Int
getRandomInt n = getStdRandom (randomR (0,n))

getRandomGroup :: IO [Agent]
getRandomGroup = do
  n <- getRandomInt 2
  case n of 0 -> return ["0"]
            1 -> return ["1"]
            _ -> return ["0","1"]

getRandomF :: IO Form
getRandomF = do d <- getRandomInt mycomplexity
                getRandomForm d

getRandomForm :: Int -> IO Form
getRandomForm 0 = do
  n <- getRandomInt 4
  case n of 0 -> return Top
            1 -> return Bot
            _ -> do m <- getRandomInt mypropsindex
                    return (PrpF (P m))

getRandomForm d = do
  n <- getRandomInt 9
  case n of
    0 -> do m <- getRandomInt mypropsindex
            return (PrpF (P m))
    1 -> do f <- getRandomForm (d-1)
            return (Neg f)
    2 -> do f <- getRandomForm (d-1)
            g <- getRandomForm (d-1)
            return (Impl f g)
    3 -> do m  <- getRandomInt myconlength
            fs <- getRandomForms (d-1) m
            return (Conj fs)
    4 -> do m  <- getRandomInt myconlength
            fs <- getRandomForms (d-1) m
            return (Disj fs)
    5 -> do i <- getRandomInt myagsindex
            f <- getRandomForm (d-1)
            return (K (show i) f)
    6 -> do i <- getRandomInt myagsindex
            f <- getRandomForm (d-1)
            return (Kw (show i) f)
    7 -> do ags <- getRandomGroup
            f <- getRandomForm (d-1)
            return (Ck ags f)
    8 -> do ags <- getRandomGroup
            f1 <- getRandomForm (d-1)
            f2 <- getRandomForm (d-1)
            return (Announce ags f1 f2)
    _ -> do f1 <- getRandomForm (d-1)
            f2 <- getRandomForm (d-1)
            return (PubAnnounce f1 f2)

getRandomForms :: Int -> Int -> IO [Form]
getRandomForms _ 0 = return []
getRandomForms d n = do f <- getRandomForm d
                        fs <- getRandomForms d (n-1)
                        return (f:fs)

mymodel :: PointedModel
mymodel = (KrM ws rel (zip ws table), 0) where
  ws    = [0..(2^(mypropsindex+1)-1)]
  rel   = ("0", map (:[]) ws) : [ (show i,[ws]) | i <- [1..myagsindex] ]
  table = foldl buildTable [[]] [P k | k<- [0..mypropsindex]]
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr<-partrows ]

myscn :: Scenario
myscn = (KnS ps (boolBddOf Top) (("0",ps):[(show i,[]) | i<-[1..myagsindex]]) , ps)
  where ps = [P 0 .. P mypropsindex]

singleTest :: IO (Bool, Bool)
singleTest = do
  f <- getRandomF
  -- print f -- uncomment this to show formulas while testing.
  singleTestWith f

singleTestWith :: Form -> IO (Bool, Bool)
singleTestWith f = do
  let a = KRIPKEDEL.eval mymodel f             -- evaluate directly on Kripke
  let b = KNSCAC.eval myscn f                  -- evaluate directly on KNS
  let c = KNSCAC.evalViaBdd myscn f            -- evaluate boolean equivalent on KNS
  let d = KRIPKEDEL.eval (knsToKripke myscn) f -- evaluate on corresponding Kripke
  let e = KNSCAC.eval  (kripkeToKns mymodel) f -- evaluate on corresponding KNS
  if or [a/=b,b/=c,c/=d,d/=e]
    then do putStr $ "Problem: " ++ show f ++ "\n         " ++ show (a,b,c,d,e) ++"\n\n"
            return (True,a)
    else    return (False,a)

test :: Int -> IO ()
test n = do (problems,truths) <- testLoop 0 0 n
            putStrLn $ show problems ++ " problems among " ++ show n ++ " formulas out of which " ++ show truths ++" were true."

testLoop :: Int -> Int -> Int -> IO (Int,Int)
testLoop p t 0 = return (p,t)
testLoop p t n = do (prob,res) <- singleTest
                    testLoop (if prob then p + 1 else p) (if res then t + 1 else t) (n-1)

pubAnnounceTest :: IO Bool
pubAnnounceTest = do
  n <- getRandomInt mypropsindex
  let f = PrpF (P n)
  g <- getRandomF
  print (PubAnnounce f g)
  let a = KRIPKEDEL.eval mymodel (PubAnnounce f g)
  putStr $ show a
  let b = KNSCAC.eval (kripkeToKns mymodel) (PubAnnounce f g)
  putStr $ show b
  let c = KNSCAC.eval (knowTransform (kripkeToKns mymodel) (actionToEvent (pubAnnounceAction ["0","1","2"] f))) g
  print c
  if a/=b || b/=c
    then do putStr $ "Problem: " ++ show g ++ "\n         "++ show (a,b,c) ++"\n\n"
            return False
    else    return True

getRandomAction :: IO PointedActionModel
getRandomAction = do
  [f,g,h] <- getRandomForms 2 3
  return (ActM [0..3] [(0,Top),(1,f),(2,g),(3,h)]
    ( ("0",[[0],[1],[2],[3]]):[(show k,[[0..3]]) | k<-[1..myagsindex] ]), 0)

singleActionTest :: IO Bool
singleActionTest = do
  myact <- getRandomAction
  f <- getRandomForm 3
  let a = KRIPKEDEL.eval (productUpdate mymodel myact) f
  let b = KNSCAC.evalViaBdd (knowTransform (kripkeToKns mymodel) (actionToEvent myact)) f
  if a /= b
    then do putStr $ "Problem: " ++ show myact
                  ++ "\n action: " ++ show (actionToEvent myact)
                  ++ "\n   form: " ++ show f
                  ++ "\n    res: " ++ show (a,b) ++ "\n\n"
            return True
    else return False

actionTest :: Int -> IO ()
actionTest n = do
  problems <- actionTestLoop 0 n
  putStrLn $ show problems ++ " problems among " ++ show n ++ " formula/action pairs."

actionTestLoop :: Int -> Int -> IO Int
actionTestLoop p 0 = return p
actionTestLoop p n = do
  problem <- singleActionTest
  actionTestLoop (if problem then p+1 else p) (n-1)
