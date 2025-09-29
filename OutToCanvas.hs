module OutToCanvas(putMessageG,putMessageT,putGrid,putMoziCl,putPlayer
                  ,clearMessage,putMozi,putWst,putChara) where

import Haste.Graphics.Canvas(Canvas,Color(RGB),Bitmap,color,font,translate,rotate
                            ,text,draw,scale,render,renderOnTop)
import Control.Monad (when)
import Define (miy,wg,hg,wt,ht,cvT,nfs,rfs
              ,State(..),Play(..),Switch(..),CInfo,Grid,Pos
              ,Mode(..),Msg,Fsize,wstIndex)
import Browser(chColors)
import PrepOutput(prepMessage,prepNormal,prepShowMap,prepLet,prepLetters,nextPQ)
import Libs(getIndex)

type Bmps = ([Bitmap],[Bitmap],[Bitmap])

putMessageG :: Canvas -> CInfo -> Bmps -> State -> IO State
putMessageG c ((cvW,cvH),_) bmps st = do 
   let sw = swc st
   if ims sw && not (imp sw) then do
     let (ch,p,q,p',q',miq,mc,ms,col,rbs,mix,gix,scx,rfs,irb,isc,iscx,nsw,nst,nst')
            = prepMessage (cvW,cvH) sw st
     if irb then mapM_ (\(ch,rd) -> 
                  putLet c col rfs rd (p',q') ch) (zip rbs [0,1..]) 
            else do
              let (itp0,itp1,msg',posx) = prepNormal isc iscx mc ms mix scx nsw nst
              when itp0 $ putMessageT c cvH (posx,miq) msg'
              when itp1 $ clearMessage c cvW gix bmps nst >>
                                       putMessageT c cvH (posx,miq) msg'
              when (not isc && not iscx) $ putLet c col nfs 0 (p,q) ch
     return nst'
   else return st

putMessageT :: Canvas -> Double -> Pos -> String -> IO ()
putMessageT c cvH (p,q) = putLetters c cvH 0 q (p,q) 

putLetters :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putLetters _ _ _ _ _ [] = return ()
putLetters c cvH cln miq (p,q) (x:xs) = do
  case x of 
    '{'   -> putNothing c cvH cln miq (p,q) xs
    '：'  -> putRubi c cvH cln miq (if miq==q then p+1 else p,if miq==q then eq else q-1) xs
                where eq = floor ((cvH-cvT)/ht)
    '\n'  -> putLetters c cvH 0 miq (p-1,miq) xs
    _     -> do let (lt,ncln,col,p',q') = prepLetters cvH cln miq p q x 
                when (lt/='@') $ putLet c col nfs 0 (p,q) lt 
                putLetters c cvH ncln miq (p',q') xs

putNothing :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putNothing _ _ _ _ _ [] = return ()
putNothing c cvH cln miq (p,q) (x:xs) = do
  case x of
    '}' -> do let (p',q') = nextPQ cvH miq (p,q)
              putLetters c cvH cln miq (p',q') xs
    _   -> putNothing c cvH cln miq (p,q) xs

putRubi :: Canvas -> Double -> Int -> Int -> Pos -> String -> IO ()
putRubi c cvH cln miq (p,q) = pRubi c miq 0 (p,q)
  where
    col = chColors!!cln
    pRubi _ _ _ _ [] = return ()
    pRubi c miq rd (p,q) (x:xs) = do
      case x of
        '：' -> let (p',q')=nextPQ cvH miq (p,q)
                 in putLetters c cvH cln miq (p',q') xs
        _    -> do putLet c col rfs rd (p,q) x 
                   pRubi c miq (rd+1) (p,q) xs

putGrid :: Canvas -> Pos -> Grid -> IO ()
putGrid c (x,y) grid = do 
  putMoziCl c
  putMozi c (head chColors) (x,y) edgeLine
  putInside (x,y+1) grid
    where gridWidth = length (head grid)
          edgeLine = "-"++replicate gridWidth '-'++"-"
          putInside (p,q) [] = putMozi c (head chColors) (p,q) edgeLine
          putInside (p,q) (g:gs) = do
            let inside = map (\(ch,tp) -> if tp==DB || tp==DF then ' ' else ch) g
            putMozi c (head chColors) (p,q) ("|"++inside++"|")
            putInside (p,q+1) gs

putPlayer :: Canvas -> Pos -> Play -> IO ()
putPlayer c pxy p = do
  let playerColor = if et p == ' ' then chColors!!1 else chColors!!2
  putMozi c playerColor pxy [pl p] 

putMoziCl :: Canvas -> IO ()
putMoziCl c = render c $ text (0,0) "" 

clearMessage :: Canvas -> Double -> Int -> Bmps -> State -> IO ()
clearMessage c cvW gix bmps st = do
  putMoziCl c
  when isMap $ do
    let (wd,cnm,pxy,p) = prepShowMap gix st
    let (_,chrs,_) = bmps
    let (chNum,anNum) = chr st
    let (wd,_) = sz st
    let chrIndex = chNum*8+anNum
    let chPos = (wd+10,miy) 
    putGrid c (gix-wd,miy) (gr p)
    putMozi c (chColors!!cnm) pxy [pl p]
    putChara c chrs cvW chPos chrIndex
      where isMap = ism$swc st 

putMozi :: Canvas -> Color -> Pos -> String -> IO ()
putMozi c col (x,y) str = renderOnTop c $ 
    mapM_ (\(ch,n)->color col$font (show nfs++"px Courier")$
      text (px*wg+wg*n,py*hg) [ch]) (zip str [0..]) 
        where (px,py) = (fromIntegral x,fromIntegral y)

putLet :: Canvas -> Color -> Fsize -> Double -> Pos -> Char -> IO ()
putLet c col fs rd (x,y) ch = do
  renderOnTop c $ color col$font (show fs++"px IPAGothic")$
    translate (px+ex,py-ext)$rotate rta$text (0,0) [ch]
      where ((px,py),(ex,ext),rta) = prepLet col fs rd (x,y) ch

putWst :: Canvas -> [Bitmap] -> Fsize -> Pos -> Char -> IO () 
putWst c wsts fs (x,y) ch = do
  renderOnTop c $ translate (px, py+5) $ scale (0.7,0.7) $ draw (wsts!!ind) (0,0)
    where ind = if ch `elem` wstIndex then getIndex ch wstIndex else 14
          (px,py) = (fromIntegral x * wg, fromIntegral y * hg)

putChara :: Canvas -> [Bitmap] -> Double -> Pos -> Int -> IO ()
putChara c chrs cvW (x,y) ind = do  
  renderOnTop c $ translate pos $ scale (2,2) $ draw (chrs!!ind) (0,0)
    where pos = (cvW-fromIntegral x * wg, fromIntegral y * hg)
