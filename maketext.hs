module Main where

import System.IO(IOMode(..), openFile, hClose, hGetContents', hSetEncoding, utf8, hPutStr)
import Data.List(transpose)
import Control.Monad (foldM)
import Data.Bifunctor(first)
import Libs(sepByChar,getIndex)

type Pos = (Int,Int)
type Size = (Int,Int)
type Mana = Char
type Cell = (Mana,Mode)
type Stage = [(Pos,Cell)]
type Def = (String,Integer)

data Mode = Fr | Bl | Ex | Mv | Pn | Wn | Cm | DB | DF deriving (Eq,Enum,Show)

txPasses :: [FilePath]
txPasses = let nameh = "Texts/fi"
               nums = [0..8]
               namel = ".txt"
            in map (\n -> nameh ++ show n ++ namel) nums

tgPass :: FilePath
tgPass = "Messages.hs"

tgPass2 :: FilePath
tgPass2 = "Stages.hs"

header :: String
header = "module Messages(initMsg,msgR,msgW,msgs) where\n\n"

header2 :: String
header2 = "module Stages(stages,evts,players,initPos,gridSize,idef) where\n\nimport Define (Stage,Evt,Size,Pos,Def,Mode(..))\n\n"

trans :: String -> String
trans cn = let cns = lines cn
            in header++ unlines (makeVar$changeLines cns)++"\nmsgs=["++init (footer cns)++"]"

trans2 :: String -> String
trans2 cn = let cns = lines cn
            in header2 ++ unlines (map (mapDataToString.makeMapData) (makeMap cns)) ++ footer2 cns

mapDataToString :: (String,[String],[String]) -> String
mapDataToString (mn,mp,dt) = init mn ++ " :: Stage\n" ++ init mn ++ " = " ++ show (makeMapList mp dt (0,0)) ++"\n"

makeMapList :: [String] -> [String] -> Pos -> Stage
makeMapList [] _ _ = [] 
makeMapList _ [] _ = []
makeMapList (m:ms) (d:ds) (_,y) = makeMapLine m d (0,y)++makeMapList ms ds (0,y+1)

makeMapLine :: String -> String -> Pos -> Stage 
makeMapLine [] _ _ = []
makeMapLine (m:ms) (d:ds) (x,y) = 
  if m=='*' || m=='@' then makeMapLine ms ds (x+1,y)
            else ((x,y),(m,toEnum (read [d])::Mode)):makeMapLine ms ds (x+1,y)

makeMapData :: String -> (String,[String],[String])
makeMapData str = let (m:d:_) = sepByChar '`' str
                      (mn:mp) = sepByChar ',' m
                      da = sepByChar ',' d
                   in (mn,map reverse (transpose mp),map reverse (transpose da))

footer2 :: [String] -> String
footer2 cns = "stages :: [Stage]\nstages = ["++tail (getStages cns) ++"]\n\n"
              ++ "evts :: [Evt]\nevts = []\n\n" 
              ++ "players :: [Char]\nplayers = " ++ show (getPlayer cns '@') ++ "\n\n"
              ++ "initPos :: [Pos]\ninitPos = " ++ show (getInitPos cns) ++"\n\n"
              ++ "gridSize :: [Size]\ngridSize = "++ show (getSize cns) ++"\n\n"
              ++ "idef :: [(Def,Int)]\nidef = " ++ show (getIdef cns)

getIdef' :: String -> [(Def,Int)]
getIdef' (_:_:_:df) = let (sn:dts) = sepByChar ' ' df 
                       in readDefs 1000 (read sn) dts

readDefs :: Integer -> Int -> [String] -> [(Def,Int)]
readDefs _ _ [] = [] 
readDefs i sn (x:xs) = let parts = sepByChar '=' x
                        in map (\p -> ((p,i),sn)) parts++readDefs (i+1) sn xs

getIdef :: [String] -> [(Def,Int)]
getIdef [] = []
getIdef (x:xs)
  |length x > 4 && take 3 x == "DEF" = getIdef' x++getIdef xs 
  |otherwise = getIdef xs

getPlayer :: [String] -> Char -> String
getPlayer [] _ = []
getPlayer (x:xs) ch
  |length x == 8 && take 7 x == "player " = getPlayer xs (last x)
  |length x > 3 && take 3 x == "map" && last x == ':' = ch:getPlayer xs '@'
  |otherwise = getPlayer xs ch

getInitPos' :: [String] -> Bool -> Pos
getInitPos' [] _ = (0,0)
getInitPos' (x:xs) b
  |x=="" = (0,0)  
  |'@' `elem` x = (fst (getInitPos' xs True),getIndex '@' x)
  |b  = first (+1) (getInitPos' xs b)
  |otherwise = getInitPos' xs b

getInitPos :: [String] -> [Pos]
getInitPos [] = []
getInitPos (x:xs)
  |length x > 3 && take 3 x == "map" && last x == ':' = getInitPos' xs False:getInitPos xs 
  |otherwise = getInitPos xs

getSize' :: [String] -> Size 
getSize' [] = (0,0) 
getSize' (x:xs)
  |x=="" = (0,0)
  |otherwise = (1+fst (getSize' xs),length x)

getSize :: [String] -> [Size] 
getSize [] = []
getSize (x:xs)
  |length x > 3 && take 3 x == "map" && last x == ':' = getSize' xs:getSize xs 
  |otherwise = getSize xs


getStages :: [String] -> String
getStages [] = []
getStages (x:xs)
  |length x > 3 && take 3 x == "map" && last x == ':' = ","++init x++getStages xs 
  |otherwise = getStages xs

changeLines :: [String] -> [String]
changeLines = map changeLine 

changeLine :: String -> String
changeLine [] = []
changeLine (x:xs) = if x=='\\' then changeProg xs else x:changeLine xs

changeProg :: String -> String
changeProg p = let ps = sepByChar ' ' p 
                in concatMap (\x -> "{"++decodePr x++"}") ps 

decodePr :: String -> String
decodePr = id 

makeMode :: [String] -> String
makeMode [] = []
makeMode (x:xs)
  | x=="" = ""
  | otherwise = ","++x++makeMode xs

makeMap' :: [String] -> String
makeMap' [] = [] 
makeMap' (x:xs)
  | x=="" = "`"++ tail (makeMode xs)
  | otherwise = ","++x++makeMap' xs

makeMap :: [String] -> [String]
makeMap [] = []
makeMap a@(x:xs)
  |x=="" = makeMap xs
  |length x > 3 && take 3 x == "map" && last x == ':' = tail (makeMap' a):makeMap xs
  |otherwise = makeMap xs
  

makeVar' :: [String] -> String
makeVar' [] = "\"" 
makeVar' (x:xs)
  |x=="" = "\"\n"
  |x=="/" = "\\n"++makeVar' xs
  |last x==':' = if x=="initMsg:" 
                    then init x++"=\""++ drop 2 (makeVar' xs) 
                    else init x++"=\"\\n"++ drop 2 (makeVar' xs)
  |otherwise = "\\n"++x++makeVar' xs 

makeVar :: [String] -> [String]
makeVar [] = []
makeVar a@(x:xs) 
  |x=="" = makeVar xs
  |length x > 3 && take 3 x == "map" && last x==':' = makeVar xs
  |last x==':' = makeVar' a:makeVar xs
  |otherwise = makeVar xs

footer :: [String] -> String
footer [] = [] 
footer (x:xs)
  | x=="" = footer xs
  | length x > 3 && take 3 x == "map" && last x==':' = footer xs
  | last x==':' = "(\""++init x++"\","++init x++"),"++footer xs
  | otherwise = footer xs

fileRead :: String ->  FilePath -> IO String
fileRead pcon flPass = do
  hin <- openFile flPass ReadMode
  hSetEncoding hin utf8
  con <- hGetContents' hin
  hClose hin
  return (pcon ++ con)

main :: IO ()
main = do
  con <- foldM fileRead "" txPasses
  hout <- openFile tgPass WriteMode
  let res = trans con
  hSetEncoding hout utf8
  hPutStr hout res
  mapM_ putStrLn $ lines res
  hClose hout
  hout2 <- openFile tgPass2 WriteMode
  let res2 = trans2 con
  hSetEncoding hout2 utf8
  hPutStr hout2 res2
  mapM_ putStrLn $ lines res2
  hClose hout2

