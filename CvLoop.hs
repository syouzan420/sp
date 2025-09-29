module CvLoop (inputLoop,mouseClick,timerEvent) where

import Haste.Graphics.Canvas(Canvas,Bitmap)
import Haste.Audio
import Control.Monad(unless,when)
import Data.List(intercalate,sort)
import Data.Maybe(fromMaybe)
import qualified Data.Map as Map
import Text.Read(readMaybe)
import Define(State(..),Play(..),Switch(..),Mode(..),LSA(..),Dir(..),CInfo,Pos,Msg
             ,miy,tiy,wg,wt)
import Stages(stages,players,initPos,gridSize)
import Grid(checkGrid,makeGrid)
import Browser(chColors,clFields,flToKc,fields,cvRatio,localStore,stringToJson)
import OutToCanvas(putMessageG,putMessageT,putGrid,putMoziCl,clearMessage
                  ,putPlayer,putMozi,putWst,putChara)
import Check(checkEv,getMessage)
import Libs(getRandomNumIO,sepByChar)
import Action(keyCodeToChar,keyChoice,keyCheck,putOut,plMove,makeChoiceMessage
             ,mkDir)
import Event(makeEvent)
import EReki (Rdt(..), reki)

type Bmps = ([Bitmap],[Bitmap],[Bitmap])
type GrPos = Pos
type PlPos = Pos 
type ChPos = Pos
type TxPos = Pos
data Positions = Ps GrPos PlPos ChPos TxPos

getPos :: CInfo -> State -> Positions
getPos ((cvW,cvH),_) st =
  let mix = floor (cvW/wt) - 1
      gix = floor (cvW/wg) - 2
      (wd,hi) = sz st
      p = player st
      grid = gr p 
      (px,py) = xy p
   in Ps (gix-wd,miy) (px+gix-wd+1,py+miy+1) (wd+10,miy) (mix+msc st,miy+hi+tiy)

timerEvent :: Canvas -> CInfo -> Bmps -> State -> IO State
timerEvent c ci bmps st = do
  let ticSt = tic st
      rtcSt = rtc st
      sw = swc st
      t = if ticSt > 298 then 0 else ticSt+1
      isChrUpdate = ism  sw && t `mod` 10 == 0 && not (ims sw) 
      nrtc = if null (rdt st) || t `mod` 20 /=0 then rtcSt else rtcSt + 1
      rst = if nrtc==30 then rekiHint st else st
      nst = rst{tic=t,rtc=nrtc}
  if igc sw then return nst else
      if isChrUpdate then drawUpdate c ci bmps nst else putMessageG c ci bmps nst

drawUpdate :: Canvas -> CInfo -> Bmps -> State -> IO State 
drawUpdate c ci@((cvW,cvH),_) bmps st = do
  let (_,chrs,_) = bmps
      (chNum,anNum) = chr st
      t = tic st
      anNum'
        | t `mod` 10 /= 0 = anNum
        | even anNum = anNum + 1
        | otherwise = anNum - 1
      chrIndex = chNum*8+anNum'
      nst = st{chr=(chNum,anNum')}
      p = player nst
      grid = gr p 
      (Ps grPos plPos chPos txPos) = getPos ci nst
  putGrid c grPos grid 
  putPlayer c plPos p
  unless ((ims . swc) nst) $  putMessageT c cvH txPos (msg nst)
  when ((ich . swc) nst) $ putMessageT c cvH txPos (makeChoiceMessage (msg nst) (map fst (chd nst)) (chn nst)) 
  unless (null (rdt nst)) $ putMozi c (chColors!!1) (1,1) (show (rtc nst))
  putChara c chrs cvW chPos chrIndex 
  return nst

mouseClick :: Canvas -> CInfo -> Bmps -> (Int,Int) -> State -> IO State
mouseClick c ci bmps (x,y) = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      cvWH = fst ci
  inputLoop c ci bmps (flToKc (clFields nx ny (fields cvWH))) 

skipMessage :: Canvas -> CInfo -> Bmps -> State -> IO State
skipMessage c ci bmps st = do
  st' <- putMessageG c ci bmps st
  let sw' = swc st'
  if imp sw' || not (ims (swc st)) then return st'{swc=sw'{ini=False}}
                                   else skipMessage c ci bmps st'

choiceMode :: Char -> State -> State
choiceMode ch st = 
  let (dlgs,mnas) = unzip (chd st)
      cn = chn st
      ncn = keyChoice (length dlgs - 1) cn ch 
   in case ncn of
        (-1) -> let nmsg = getMessage [] (mnas!!cn)
                 in st{msg=nmsg,swc=(swc st){ims=True,ich=False,imp=False}}
        (-2) -> st
        _    -> st{chn=ncn}

rekiAction :: State -> IO State
rekiAction st = do
  let pl = player st 
      rekSt = rek st 
      stageNum = sn  pl
      randomG = rgn pl
  case rekSt of
    [n,l,r,jp] -> do
       let qt = fromMaybe 1 (readMaybe n) -- question type (1 or 2)
           qLng = length r -- number of questions
       (mondai,jun,ng) <- reki qt qLng randomG
       let ndef = [((l,333),stageNum),((makeRekiAns r jun,333),stageNum)]
           nrdt = zip mondai r
           emsSt = delRekMessages r (ems st)
           nmsg = makeRekiMon nrdt 
           st' = st{player=pl{edf=edf pl++ndef,rgn=ng}, ems=emsSt++nmsg
                   ,rek=[], rdt=nrdt, rtc=0}
           codeJp = ("e.==.m1:" ++ jp) : makeRekiJp r
           nst = foldl (flip makeEvent) st' codeJp
       return nst
    _ -> return st{rek=[]}

rekiHint :: State -> State
rekiHint st = let rdtSt = rdt st
                  emsSt = ems st
                  emsSt' = delRekMessages (map snd rdtSt) emsSt
                  nems = emsSt' ++ makeRekiHint rdtSt
               in st{ems=nems} 

rekiCorrect :: State -> State
rekiCorrect st = let rdtSt = rdt st
                     rtcSt = rtc st
                     rtlSt = rtl st
                     emsSt = ems st
                     emsSt' = delRekMessages (map snd rdtSt) emsSt
                     nems = emsSt' ++ makeRekiCorrect rdtSt
                  in st{player=(player st){edf=[]},ems=nems,rdt=[]
                       ,rtl=rtlSt++[rtcSt]} 

delRekMessages :: [Char] -> [(String,Msg)] -> [(String,Msg)]
delRekMessages chs emsSt =
  let keys = map (: "Rk") chs
      mapList = foldl (flip Map.delete) (Map.fromList emsSt) keys
   in Map.toList mapList

makeRekiJp :: String -> [String]
makeRekiJp = map (\ch ->"e.e" ++ [ch] ++ ".m0:" ++ [ch] ++ "Rk") 

makeRekiMon :: [(Rdt,Char)] -> [(String,Msg)]  
makeRekiMon = map (\(Rdt _ mon _ _,ch)-> (ch:"Rk",mon))

makeRekiHint :: [(Rdt,Char)] -> [(String,Msg)]  
makeRekiHint = map (\(Rdt _ mon hint _,ch)-> (ch:"Rk",mon++" >>"++hint))

makeRekiCorrect :: [(Rdt,Char)] -> [(String,Msg)]  
makeRekiCorrect = map (\(Rdt nen mon hint exp,ch) ->
                           (ch:"Rk",show nen++"年 "++mon++" >>"++hint++" >>"++exp))

makeRekiAns :: String -> [Int] -> String
makeRekiAns str = map (\i -> fromMaybe ' ' (lookup i (zip [1..] str)))

drToNum :: Dir -> Int
drToNum Up = 2
drToNum Dw = 0
drToNum Lf = 6
drToNum Rt = 4
drToNum _ = 0

lastN :: Int -> String -> String
lastN i str = let lng = length str in drop (lng-i) str

mapAction :: Canvas -> CInfo -> Bmps -> Int -> Char -> State -> IO State
mapAction c ci bmps gix ch st = do
  let irkSt = not $ null $ rek st
  rst <- if irkSt then rekiAction st else return st
  let p@(Play xyP _ _ _ _ _ edfP rgnP elgP _ iscP) = player rst
  sequence_ [print (evt st),print (ecs st), print (mem st),print elgP,print iscP,print (jps st),print edfP,print (rtl st)]
  (_,nrg) <- getRandomNumIO (5,rgnP)
  let nxy = keyCheck (sz st) xyP ch 
      ndr = mkDir xyP nxy
      (chNum,anNum) = chr rst
      nchr = if ndr==dr p then (chNum,anNum) else (chNum,drToNum ndr)
      p' = plMove nxy p{dr=ndr}
      p'' = if ch==' ' then putOut p' else p'
      st' = checkEv 0 (elg p'') (evt rst) rst{player=p''{rgn=nrg}, chr=nchr}
      irkComp = not (null (rdt st')) && lastN 2 (elg p'') == "=="
      st'' = if irkComp then rekiCorrect st' else st'
  nst <- drawUpdate c ci bmps st'' 
  let nsw = swc nst
  sData <- case ch of
             's' -> localStore Save "savedata" (makeSaveData st) 
             'r' -> localStore Load "savedata" ""
             'd' -> localStore Remv "savedata" ""
             _   -> return "---"
  if ch=='r' && sData/="loadError" then loadState c ci sData nst else do 
    print sData
    if ils nsw || ch=='n' then nextStage c ci bmps nst{swc=nsw{ims=False}} 
                          else return nst 

inputLoop :: Canvas -> CInfo -> Bmps -> Int -> State -> IO State 
inputLoop c ci@((cvW,cvH),_) bmps kc st
  | iniSt = return st
  | igcSt = return st
  | imsSt && not impSt = skipMessage c ci bmps st{swc=sw{ini=True}} 
  | impSt = if ichSt then drawUpdate c ci bmps (choiceMode ch st) 
                     else return st{swc=sw{imp=False}}
  | ismSt = mapAction c ci bmps gix ch st
  | otherwise = return st 
       where sw = swc st
             iniSt = ini sw; impSt = imp sw; imsSt = ims sw
             ichSt = ich sw; ismSt = ism sw; igcSt = igc sw
             mix = floor (cvW/wt) - 1; gix = floor (cvW/wg) - 2
             ch = keyCodeToChar kc

makeSaveData :: State -> String
makeSaveData st =
  let stageData = sn$player st
      evtData = intercalate "," $ concatMap (\(tr,tg) -> [tr,tg]) (evt st)
      ecsData = intercalate "," $ map show (ecs st)
   in "\""++intercalate "~" [show stageData,evtData,ecsData]++"\""

loadState :: Canvas -> CInfo -> String -> State -> IO State
loadState _ _ "" st = return st
loadState c ci str st = do
  let dt = if head str=='\"' then tail$init str else str
      dts = sepByChar '~' dt
      nsn = read (head dts)
      evtStr = dts!!1
      nevt = listToTupples (sepByChar ',' evtStr)
      ecsStr = dts!!2
      necs = map read $ sepByChar ',' ecsStr
      nsz = gridSize!!nsn
      npl = players!!nsn
      nxy = initPos!!nsn
      ngr = makeGrid nsz (stages!!nsn)
      nst = st{player=(player st){xy=nxy, gr=ngr, pl=npl, et=' ', sn=nsn},sz=nsz,evt=nevt,ecs=necs}
  return nst

listToTupples :: [String] -> [(String,String)]
listToTupples [] = []
listToTupples [x] = []
listToTupples (x:y:xs) = (x,y):listToTupples xs

nextStage :: Canvas -> CInfo -> Bmps -> State -> IO State 
nextStage c ci bmps st = do
  let p = player st
      js = jps st
      nsn = if js<0 then sn p + 1 else js
      maxSn = length stages
      gc = nsn == maxSn
      nlg = elg p++'c':show (sn p)
  if gc then gameClear c st{swc=(swc st){igc=True}}
        else do
          let nsz=gridSize!!nsn
              grid=makeGrid nsz (stages!!nsn)
              iwn=checkGrid (' ',Wn) grid
              np = p{xy=initPos!!nsn, gr=grid, pl=players!!nsn, et=' ',sn=nsn,
                     elg=nlg,isc=False,iw=iwn}
          inputLoop c ci bmps 64 st{sz=nsz,player=np,msg="",jps = -1,swc=(swc st){ils=False,igc=False}}

gameClear :: Canvas -> State -> IO State 
gameClear c st = do putMoziCl c
                    let col=head chColors
                    putMozi c col (3,8) "Coding : yokoP"
                    putMozi c col (3,12) "First Up : 2024 12 24" 
                    putMozi c col (2,17) "Thank you!"
                    let nsz=head gridSize
                        p = player st
                        np=p{xy = head initPos, gr=makeGrid nsz (head stages),
                             pl=head players,et=' ',sn=0,elg="",isc=False}
                    return st{sz=nsz,player=np}

