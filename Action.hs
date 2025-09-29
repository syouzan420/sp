module Action(keyCodeToChar,keyChoice,keyCheck,putOut,plMove
             ,makeChoiceMessage,mkDir) where

import Define(State(..),Play(..),Switch(..),Mode(..),Dir(..),Pos,Size,Grid,Msg)
import Stages(stages,players,initPos,gridSize,idef,evts)
import FiFunc(funcPon,stagePon,doNothing)
import Grid(intoGrid,fromGrid,sizeGrid,makeGrid)
import Messages(initMsg)
import Check(checkDef,checkEq)
import Libs(getIndex,getRandomNum)

keyCheck :: Size -> Pos -> Char -> Pos 
keyCheck (wd,hi) (x,y) ch  
  | ch=='j'||ch=='P' = if hi==y+1 then (x,y) else (x,y+1)
  | ch=='k'||ch=='H' = if 0>y-1 then (x,y) else (x,y-1)
  | ch=='h'||ch=='K' = if 0>x-1 then (x,y) else (x-1,y)
  | ch=='l'||ch=='M' = if wd==x+1 then (x,y) else (x+1,y)
  | otherwise = (x,y) 

keyChoice :: Int -> Int -> Char -> Int
keyChoice mx cn ch
  | ch=='j'||ch=='P'||ch=='h'||ch=='K' = if cn==mx then 0 else cn+1
  | ch=='k'||ch=='H'||ch=='l'||ch=='M' = if cn==0 then mx else cn-1
  | ch==' ' = -1
  | otherwise = -2

fpon :: Char -> Char -> Char
fpon p e = let (cs,fs)=unzip funcPon 
               f = fs!!getIndex p cs
            in f e

spon :: Int -> Char -> Char -> Char
spon i e t = let (sn,fs)=unzip stagePon
                 f = if i `elem` sn then fs!!getIndex i sn else doNothing
              in f e t

putOut :: Play -> Play 
putOut p =
  let (Play pos grid _ pla eat snum edef _ lg _ _) = p
      (ch,tp) = fromGrid pos grid 
      iout = eat/=' ' && ch==' '
      ipn = tp==Pn
      eat' = if iout then ' ' else eat
      ch' = let fch = fpon pla eat in if iout then fch else 
                                        if ipn then spon snum fch ch else ch
      grid' = intoGrid pos (ch',tp) grid 
      def = checkDef snum (idef++edef) grid'
      (isc',_) = checkEq def grid'
      lg' 
        | isc' = "==" 
        | iout = 'o':[ch'] 
        | ipn = 'p':[ch']
        | otherwise = ""
   in p{gr=grid',et=eat',isc=isc',elg=lg++lg'}

plMove :: Pos -> Play -> Play 
plMove (x,y) p = 
  let (Play mpos grid _ pla eat snum edef gen lg iwn is) = p
      (ch,tp) = fromGrid (x,y) grid 
      fps = map fst funcPon
      ifp = eat==' ' && ch `elem` fps && tp==Fr
      ieat = eat==' ' && ch/=' ' && (tp==Fr||tp==DF) && not ifp
      ibum = (tp==Bl||tp==DB||tp==Wn)
      iex = tp==Ex
      eat' = if ieat then ch else eat
      pla' = if ifp then ch else pla 
      ch' 
        |ieat = ' '
        |ifp = pla
        |otherwise = ch
      grid' = intoGrid (x,y) (ch',tp) grid
      imv = tp==Mv || (tp==Pn && eat==' ')
      grid'' = if imv then obMove mpos (x,y) grid' else grid'
      ngrid = if iwn then wnMove gen (x,y) grid'' else grid''
      (x',y')=if (imv&&ngrid==grid')||ibum then mpos else (x,y)
      (isc',lf) = if imv then checkEq (checkDef snum (idef++edef) ngrid) ngrid
                         else (is,"")
      lg' 
        | ieat = 'e':[ch]
        | ifp = 'f':[ch] 
        | imv&&isc' = "==" 
        | imv&&mpos/=(x',y') = 'v':[ch]
        | tp==Pn = 'n':[ch] 
        | ibum = if ch=='=' then 'b':(ch:show y) else 'b':[ch]
        | iex = 'u':[ch] 
        | otherwise = ""
   in p{xy=(x',y'),gr=ngrid,pl=pla',et=eat',isc=isc',elg=lg++lg'} 

mkDir :: Pos -> Pos -> Dir
mkDir (x0,y0) (x1,y1)
  |x1>x0 = Rt
  |x0>x1 = Lf
  |y1>y0 = Dw
  |y0>y1 = Up
  |otherwise = Cn

obMove :: Pos -> Pos -> Grid -> Grid
obMove mpos (x,y) grid =
  let gline = grid!!y
      (ch,tp) = gline!!x 
      ngrid = intoGrid (x,y) (' ',Fr) grid 
      dir = mkDir mpos (x,y)
      (x',y') = case dir of
                  Up -> if y==0 then (-1,-1) else (x,y-1)
                  Dw -> if y==length grid-1 then (-1,-1) else (x,y+1)
                  Lf -> if x==0 then (-1,-1) else (x-1,y)
                  Rt -> if x==length gline-1 then (-1,-1) else (x+1,y)
      tgline = if y'==(-1) then [] else ngrid!!y'
      (tch,_) = if x'==(-1) then (' ',Fr) else tgline!!x'
      imv = x'/=(-1) && tch==' '
      ngline' = take x' tgline++[(ch,tp)]++drop (x'+1) tgline
   in if imv then take y' ngrid ++[ngline']++ drop (y'+1) ngrid
             else grid

wnMove :: Int -> Pos -> Grid -> Grid
wnMove gen pos grid = wnMove' gen (0,0) grid pos grid
  where (sx,sy) = sizeGrid grid 
        wnMove' _ _ ngrid _ [] = ngrid
        wnMove' g (x,y) ngrid pos (((ch,tp):xs):ys)
          | tp==Wn = 
              let (n,g') = getRandomNum (5,g) 
                  (x',y') = case n of
                              0->(x,y); 1->(x-1,y); 2->(x,y-1); 3->(x+1,y); 4->(x,y+1)
                              _->(x,y)
                  imv = (x'>=0 && x'<sx && y'>=0 && y'<sy && (x',y')/=pos)
                  ch' = if imv then fst$fromGrid (x',y') ngrid else 'x'
                  (nx,ny) = if ch'==' ' && imv then (x',y') else (x,y)
                  ngrid' = if (nx,ny)==(x,y) 
                      then ngrid else intoGrid (x,y) (' ',Fr) (intoGrid (nx,ny) (ch,tp) ngrid)
               in if null xs then wnMove' g' (0,y+1) ngrid' pos ys
                             else wnMove' g' (x+1,y) ngrid' pos (xs:ys)
          | otherwise = if null xs then wnMove' g (0,y+1) ngrid pos ys
                                   else wnMove' g (x+1,y) ngrid pos (xs:ys)

keyCodeToChar :: Int -> Char
keyCodeToChar kc = case kc of
                     68 -> 'd';
                     72 -> 'h'; 74 -> 'j'; 75 -> 'k'; 76 -> 'l'; 78 -> 'n';
                     82 -> 'r'; 83-> 's';
                     _  -> toEnum kc

makeChoiceMessage :: Msg -> [String] -> Int -> Msg 
makeChoiceMessage omsg dlgs cn = let ndlgs = makeDialogs dlgs cn
                                  in omsg ++ "\n\n" ++ concatMap (++"\n\n") ndlgs

makeDialogs :: [String] -> Int -> [String]
makeDialogs dlgs cn = makeDialogs' dlgs cn 0
  where makeDialogs' [] _ _ = []
        makeDialogs' (x:xs) cn i 
          |cn==i =  if head x=='*' then (' ':x):nmd else ('*':x):nmd
          |head x=='*' = (' ':tail x):nmd
          |otherwise = (' ':x):nmd
                       where nmd = makeDialogs' xs cn (i+1)

