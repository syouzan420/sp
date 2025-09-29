module Event (makeEvent) where

import Data.List(delete)
import Data.Maybe(fromMaybe)
import Text.Read(readMaybe)
import Define (State(..),Switch(..),Play(..),Mode(..))
import Grid(changeGridType,intoGrid,clFromGrid,fromGrid,posGrid)
import Libs(sepByChar,getIndex,concatWith)

makeEvent :: String -> State -> State
makeEvent scr st = 
  let (f:es) = sepByChar '.' scr
   in case f of
        "e" -> addEvent es st
        "d" -> delEvent es st
        "da" -> delAllEvent st
        "ct" -> changeType es st 
        "p" -> putCell es st
        "c" -> clearCell es st
        "cleq" -> clearEqual st
        "m" -> addMemory es st
        "if" -> makeDecision es st
        "ch" -> makeChoice es st{chd=[]}
        "rk" -> setReki es st
        "rt" -> rekiTimeShow es st
        "rs" -> rekiScoreShow st
        "sm" -> showMap st
        "hm" -> hideMap st
        _   -> st

insertMes :: String -> State -> State
insertMes str st = let msgSt = msg st
                       mctSt = mct st
                       nmsg = take mctSt msgSt ++ str ++ drop mctSt msgSt
                    in st{msg=nmsg}

rekiScoreShow :: State -> State
rekiScoreShow st = let rtlSt = rtl st
                       score = 600 - sum rtlSt
                    in insertMes (show score) st

rekiTimeShow :: [String] -> State -> State
rekiTimeShow xs st = foldl (\st a -> insertMes (show (rtl st!!read a)) st) st xs

showMap :: State -> State
showMap st = st{swc=(swc st){ism=True}}

hideMap :: State -> State
hideMap st = st{swc=(swc st){ism=False}}

clearEqual :: State -> State 
clearEqual st = let p = player st
                 in st{player=p{gr=clFromGrid '=' (gr p)}} 

clearCell :: [String] -> State -> State
clearCell [] st = st
clearCell (a:xs) st = let p = player st
                          (x':y':_) = sepByChar ',' a
                          x = read x'::Int; y = read y'::Int
                       in clearCell xs st {player = p{gr=intoGrid (x,y) (' ',Fr) (gr p)}}

putCell :: [String] -> State -> State 
putCell [] st = st 
putCell (a:b:xs) st = let p = player st
                          (x':y':_) = sepByChar ',' a
                          (chs:tps:_) = sepByChar ',' b
                          x = read x'::Int; y = read y'::Int
                          ch = head chs; tp = readType tps
                       in putCell xs st{player=p{gr=intoGrid (x,y) (ch,tp) (gr p)}}

readType :: String -> Mode
readType str = case str of "Fr"->Fr; "Bl"->Bl; "Ex"->Ex; "Mv"->Mv; "Pn"->Pn; "Wn"->Wn; "Cm"->Cm; "DB"->DB; "DF"->DF;

changeType :: [String] -> State -> State 
changeType [] st = st 
changeType (a:b:xs) st = let p = player st
                             tp = readType b
                          in changeType xs st{player=p{gr=changeGridType (head a,tp) (gr p)}}

addEvent :: [String] -> State -> State
addEvent [] st = st
addEvent (a:b:xs) st = addEvent xs st{evt=(a,b):evt st,ecs=0:ecs st}

delAllEvent :: State -> State
delAllEvent st = st{evt=[]}

delEvent :: [String] -> State -> State
delEvent [] st = st
delEvent (x:xs) st = let evs = evt st
                         cs = ecs st
                         evks = map fst evs
                         idel = elem x evks
                         ind = if idel then getIndex x evks else (-1)
                         nevt = if idel then delFrom ind evs else evs
                         necs = if idel then delFrom ind cs else cs
                      in delEvent xs st{evt=nevt,ecs=necs}

delFrom :: Int -> [a] -> [a]
delFrom id lst = take id lst ++ drop (id+1) lst

addMemory :: [String] -> State -> State
addMemory [] st = st
addMemory (k:v:xs) st = let memSt = mem st 
                            tv = fromMaybe "" $ lookup k memSt
                            nmem = if tv=="" then memSt else delete (k,tv) memSt
                         in addMemory xs st{mem=(k,evalString st v):nmem}

makeDecision :: [String] -> State -> State
makeDecision [] st = st
makeDecision (m:c:xs) st
  | m `elem` ks = if c==vs!!getIndex m ks then makeEvent ts st else fsst
  | otherwise = fsst
  where (ks,vs) = unzip (mem st)
        (ts:fs) = sepByChar '/' (concatWith '.' xs)
        fsst = if null fs then st else makeEvent (head fs) st

makeChoice :: [String] -> State -> State
makeChoice [] st = st{swc=(swc st){ich=True,imp=True}}
makeChoice (x:xs) st = let (c:d:_) = sepByChar ',' x 
                        in makeChoice xs st{chd=chd st++[(c,d)]}

setReki :: [String] -> State -> State
setReki es st = st{rek=es}
--------------------------------------------------------------------

evalString :: State -> String -> String
evalString st = unwords.execParts st [].sepByChar '_' 

execParts :: State -> [String] -> [String] -> [String]
execParts _ acc [] = acc 
execParts st acc (x:xs) = 
  let def = lookup x definitions
      code = fromMaybe ["empty"] def
   in if code==["empty"] then execParts st (acc++[x]) xs 
                         else let args = reverse $ zip (reverse acc) (reverse code)
                                  alng = length args
                                  nacc = reverse$drop alng (reverse acc)
                               in execParts st (nacc ++ [execCode st x (map fst args)]) xs

definitions :: [(String,[String])]
definitions = [("getch",["p","q"]),("getpos",["ch","tp"])
              ,("==",["a","b"]),("&&",["a","b"]),("||",["a","b"])]

execCode :: State -> String -> [String] -> String
execCode st str args =
  case args of
    [a0,a1] -> case str of
          "getch" -> let (ch,_) = fromGrid (read a0,read a1) ((gr.player) st)
                      in [ch]
          "getpos" -> let pos = posGrid (head a0,read a1) ((gr.player) st)
                       in show pos
          "==" -> if a0==a1 then "T" else "F"
          "&&" -> if a0=="T" && a1=="T" then "T" else "F"
          "||" -> if a0=="T" || a1=="T" then "T" else "F"
          _ -> ""
    _other -> ""
