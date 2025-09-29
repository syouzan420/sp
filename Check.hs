module Check (checkDef,checkEq,checkEv,trEvent,getMessage) where

import Data.Array (listArray, (!))
import Define (Grid,Def,Evt,State(..),Play(..),Switch(..),Mode(Fr),Msg)
import Stages 
import Messages(msgs)
import Libs (isNum,isChar,getIndex,sepByChar)
import Grid
import Siki (siki)

data WhichIsChar = LFT | RIT | OTH deriving (Eq,Show)

checkDef :: Int -> [(Def,Int)] -> Grid -> [Def]
checkDef _ _ [] = []
checkDef stn df (g:gs) = 
  let (chs,_) = unzip g       -- ([Char],[Mode])
      ie = elem '=' chs
      (lf,rt) = if ie then sepeq chs else ([],[])
      (dfs,stgs) = unzip df   -- ([Def],[Int])
      (strs,exp) = unzip dfs  -- ([String],[Integer])
      stgA = listArray (0,length df - 1) stgs
      expA = listArray (0,length dfs - 1) exp
      indl = getIndex lf strs
      indr = getIndex rt strs
      idfl = elem lf strs && ((stgA!indl)==stn)
      idfr = elem rt strs && ((stgA!indr)==stn)
      exl = expA!indl
      exr = expA!indr
      addl 
        | idfl && not idfr = [(lf,exl)]
        | not idfl && idfr = [(rt,exr)]
        | idfl && idfr = [(lf,exl),(rt,exr)]
        | otherwise = []
      idf = idfl || idfr
      d = whichIsChar idf (lf,rt) 
      checkNext = checkDef stn df gs
   in if addl/=[] then addl++checkNext else 
        if ie&&(d/=OTH) then checkLine d (lf,rt):checkNext else checkNext 

whichIsChar :: Bool -> (String, String) -> WhichIsChar
whichIsChar idf (lf,rt)
  | isChar lf && not idf && rt/="" && isNum rt = LFT  
  | isChar rt && not idf && lf/="" && isNum lf = RIT 
  | otherwise = OTH 

checkLine :: WhichIsChar -> (String, String) -> Def 
checkLine LFT (lf,rt) = (lf,read rt)
checkLine RIT (lf,rt) = (rt,read lf)
checkLine _ _ = ("",0)

checkEq :: [Def] -> Grid -> (Bool,String)
checkEq def grid =
  let wheq l [] = if l=="" then (False,"") else (True,l)
      wheq l (g:gs) =
        let (chs,_) = unzip g
            ie = elem '=' chs
         in if ie then let (iq,left) = checkLine chs
                           left' = if l=="" then left else l++" "++left 
                        in if iq then wheq left' gs else (False,"")
                  else wheq l gs
      checkLine str =  
        let (lf,rt) = sepeq str
         in if rt/="" && siki def lf==siki def rt then (True,lf) else (False,"")
   in wheq "" grid 

rmsp :: String -> String
rmsp [] = []
rmsp (x:xs) = if x==' ' then rmsp xs else x:rmsp xs

sepeq :: String -> (String,String)
sepeq str = if '=' `elem` str then 
                let (l:r:_) = sepByChar '=' str
                    lw = words l; rw = words r
                    lf = if null lw then "" else last lw
                    rt = if null rw then "" else head rw
                 in (lf,rt)
                             else (str,"")

checkEv :: Int -> String -> [Evt] -> State -> State 
checkEv _ _ [] st = st 
checkEv i lg ((e,t):xs) st =
  let p = player st
      iand = elem '&' e 
      acs = sepByChar '&' e
      ne = head acs
      ic = (not iand || chAnd (tail acs))
      chAnd [] = True
      chAnd ((c:ns):xs) = (case c of
             's' -> sn p==(read ns::Int)
             'c' -> isc p 
             _   -> True 
                          ) && chAnd xs
      le = length ne
      ll = drop (length lg - le) lg
      ne' = if last ne=='?' then init ne else ne
      ll' = if last ne=='?'&&ll/="" then init ll else ll 
      (tgt,ind) = if ne'==ll' && ic || ne'=="X" then (t,i) else ("",i) 
   in if tgt=="" then checkEv (i+1) lg xs st
                 else let nst = trEvent ind tgt st
                       in if length (ecs nst)==length (ecs st)
                              then checkEv (i+1) lg xs nst else nst

getMessage :: [(String,Msg)] -> String -> String
getMessage emsg mna = let (ns,ms) = unzip (msgs++emsg)
                       in if mna `elem` ns then ms!!getIndex mna ns else "" 

trEvent :: Int -> String -> State -> State
trEvent i ev@(e:es) st =
  let cs = ecs st 
      csa = listArray (0,length cs - 1) cs
      c = csa!i
      st' = 
        case e of
          'm' -> let (nc,na,nes) = evRead c es 
                     evna = listArray (0, length evn - 1) evn
                     (t,_) = evna!i 
                     iend = nes=="" 
                     nevt = if iend then delFrom i evn else insTo i (t,e:nes) evn
                     necs = if iend then delFrom i cs else insTo i nc cs
                     emsSt = ems st
                     nmsg = getMessage emsSt na
                  in st{msg=nmsg,evt=nevt,ecs=necs,swc=sw{ims=True}}
          'r' -> let stn = sn p 
                     igs = gridSize!!stn
                     ecs' = map (*0) cs 
                     np = p{xy=initPos!!stn,gr=makeGrid igs (stages!!stn),
                            pl=players!!stn,et=' ',sn=stn}
                  in st{sz=igs,player=np,ecs=ecs',msg=getMessage [] "msgR"
                       ,swc=sw{ims=True}}
          'w' -> let igs = head gridSize
                     ecs' = map (*0) cs 
                     np = p{xy=head initPos,gr=makeGrid igs (head stages)
                           ,pl=head players,et=' ',sn=0}
                  in st{sz=igs,player=np,ecs=ecs',msg=getMessage [] "msgW"
                       ,swc=sw{ims=True}}
          't' -> let (nc,na,_) = evRead c es
                     iend = nc==0
                     tg = if iend then na else ""
                     necs = if iend then insTo i (c+1) cs else insTo i nc cs 
                     st' = st{ecs=necs}
                  in if tg=="" then st' else trEvent i tg st'
          'a' -> let (ch:po) = es
                     (cx,cy) = sepeq po
                     (x,y) = (read cx,read cy)
                     ngrid = intoGrid (x,y) (ch,Fr) (gr p) 
                  in st{player=p{gr=ngrid}}
          's' -> st{player=p{gr=toSee$gr p}}
          'h' -> st{player=p{gr=toHide$gr p}}
          'j' -> if null es then st{jps= -1}                -- Jump Stage 
                            else if head es=='l' then 
                                let nevt = delFrom i evn
                                    necs = delFrom i cs
                                 in st{jps=read (tail es)::Int,evt=nevt
                                      ,ecs=necs,swc=sw{ils=True}}
                                                 else st{jps=read es::Int} 
          'l' -> let nevt = delFrom i evn
                     necs = delFrom i cs
                  in st{evt=nevt,ecs=necs,swc=sw{ils=True}}   -- Leave Stage
          _   -> st
   in st'{player=(player st'){elg=elg p++ev}}
  where p = player st
        evn = evt st
        sw = swc st

insTo :: Int -> a -> [a] -> [a]
insTo id elm lst = take id lst ++ [elm] ++ drop (id+1) lst

delFrom :: Int -> [a] -> [a]
delFrom id lst = take id lst ++ drop (id+1) lst

evRead :: Int -> String -> (Int,String,String)
evRead c es =
  let (co:na:xs) = sepByChar ':' es
      im = (c+1)==if co=="!" then (-1) else (read co::Int)  
   in if im then if null xs then (0,na,"") else (0,na,init$concatMap (++":") xs) 
            else (c+1,na,es)

----
