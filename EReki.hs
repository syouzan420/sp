module EReki (Rdt(..), reki, sortNens) where

import Data.Array (listArray, (!))
import Data.Monoid ((<>))

import Reki (rekiDoc, rekiDoc2)
import Libs (getRandomNumIO,sepByChar)

type Nen = Int
type Koto = String 
type Hint = String 
type Content = String 
data Rdt = Rdt !Nen !Koto !Hint !Content deriving (Eq,Show)

sortNens :: [(Int,a)] -> [(Int,a)]
sortNens [] = []
sortNens ((x,a):xs) = 
    sortNens (smaller xs) <> [(x,a)] <> sortNens (larger xs)
  where smaller ls = [(p,q)|(p,q)<-ls,p<x]
        larger ls = [(p,q)|(p,q)<-ls,p>=x]

makeJun :: [Rdt] -> [Int]
makeJun rdt = let nens = map (\(Rdt n _ _ _) -> n) rdt
               in map snd (sortNens (zip nens [1,2..]))  

getRan :: Int -> Int -> IO (Int,Int)
getRan i g = getRandomNumIO (i+1,g)

delFromList :: Int -> [a] -> [a]
delFromList i ls = if length ls < i+1 then ls else take i ls <> drop (i+1) ls 

selectData :: Int -> Int -> [a] -> IO ([a],Int) 
selectData 0 g _ = return ([],g) 
selectData i g rdt = do 
  let maxI = length rdt - 1
  (rn,ng) <- getRan maxI g
  let rdtA = listArray (0,maxI) rdt 
      dt = rdtA!rn
      dts = delFromList rn rdt
  sdts <- selectData (i-1) ng dts
  return (dt:fst sdts,ng)

reki :: Int -> Int -> Int -> IO ([Rdt],[Int],Int) 
reki t i g = do
  let txs = lines (if t==2 then rekiDoc2 else rekiDoc) 
  let rdts = map makeRData txs
  (mondai,ng) <- selectData i g rdts 
  let jun = makeJun mondai
  return (mondai,jun,ng)

makeRData :: String -> Rdt
makeRData tx =
  let sps = sepByChar ',' tx
   in case sps of
        []                -> Rdt 0 "" "" "" 
        [nen]             -> Rdt (read nen) "" "" "" 
        [nen,mon]         -> Rdt (read nen) mon "noHint" "noContent" 
        [nen,mon,hin]     -> Rdt (read nen) mon hin "noContent"
        [nen,mon,hin,con] -> Rdt (read nen) mon hin con
        _other            -> Rdt 0 "" "" "" 
