module PrepOutput(prepMessage,prepNormal,prepLetters,prepLet,prepShowMap,nextPQ) where

import Define (miy,tiy,wg,hg,wt,ht,cvT,nfs,rfs
              ,State(..),Play(..),Switch(..),Mode(..),Pos)
import Browser (chColors)
import Event (makeEvent)
import Action (makeChoiceMessage)
import Libs (getInside)

prepMessage (cvW,cvH) sw st =
  let ms = msg st; mc = mct st                      -- messages and message count    O
      ml = length ms-1 
      h = if ism sw then snd (sz st) + tiy else 0     -- message initial height
      mix = floor (cvW/wt) - 1                      -- message initial x             O
      gix = floor (cvW/wg) - 2                      -- grid initial x                O
      miq = miy+h
      (p,q) = if mc==0 then (mix,miq) else mps st   -- message position              O
      tmsg = take (mc+1) ms                         -- showing message 
      lmsg = if null tmsg then ' ' else last tmsg   -- last char of showing messages
      ch = case lmsg of '、' -> ' '; '。' -> ' '; '}' -> ' ';  _ -> lmsg          -- O 
      (ic,ir,ip,irb,isc) = (ch=='「', ch=='\n', lmsg=='。', ch=='：', ch=='{')
      cln | ir = 0 | ic = 1 | otherwise = mcl st
      col = chColors!!cln
      rbs = if irb then getInside '：' mc ms else ""
      scr = if isc then getInside '}' mc ms else ""
      cta | irb = length rbs + 2 | isc = length scr + 2 | otherwise = 1
      nmct = if mc+cta > ml then 0 else mc+cta      -- new message count
      nims = mc+cta <= ml                           -- next message show?
      npos
        |irb = (p,q)
        |ir = (p-1,miq)
        |otherwise = nextPQ cvH miq (p,q) 
      iscx = fst npos==1 && fst npos/=p
      st' = st{mct=nmct, swc=sw{imp=ip}}
      nst = if isc then makeEvent scr st' else st'
      nsw = swc nst
      scx = if mc==0 then 0 else msc nst
      npos' = if iscx then (p,miq) else npos
      nmsc = if iscx then scx+1 else scx
      eq = floor ((cvH-cvT)/ht)
      p' = if miq==q then p+1 else p
      q' = if miq==q then eq else q-1
      nst' = nst{mps=npos',mcl=cln,msc=nmsc,swc=nsw{ims=nims}}
   in (ch,p,q,p',q',miq,mc,ms,col,rbs,mix,gix,scx,rfs,irb,isc,iscx,nsw,nst,nst') 

prepNormal isc iscx mc ms mix scx nsw nst =
    let itp0 = isc && ich nsw
        itp1 = not isc && iscx
        msg'
          | itp0 = let (dlgs,_) = unzip (chd nst)
                    in makeChoiceMessage (msg nst) dlgs (chn nst) 
          | itp1 = take (mc+1) ms
          | otherwise = ""
        posx
          | itp0 = mix+scx
          | itp1 = mix+scx+1
          | otherwise = 0
     in (itp0, itp1, msg', posx) 

prepLetters cvH cln miq p q ch = 
   let lt = case ch of '、' -> '@'; '。' -> '@'; '*' -> '@';  _ -> ch 
       ncln = case ch of '「' -> 1; '*'  -> 2; _    -> cln
       col = chColors!!ncln
       (p',q') = nextPQ cvH miq (p,q)
    in (lt,ncln,col,p',q')

prepShowMap gix st =
    let p = player st 
        (wd,_) = sz st
        (x,y) = xy p 
        pxy = (x+1+gix-wd,y+miy+1)
        cnm = if et p==' ' then 1 else 2
     in (wd,cnm,pxy,p)

prepLet col fs rd (x,y) ch =
  let irt = rtChar ch
      (p,q) = (fromIntegral x,fromIntegral y)
      fsd = fromIntegral fs
      nfsd = fromIntegral nfs
      rfsd = fromIntegral rfs
      (px,py) = if fs==rfs then (p*wt+nfsd,q*ht+rfsd*(rd-1))
                            else (p*wt,q*ht)
      rta = if irt then pi/2 else 0
      ex = if irt then nfsd/6 else 0
      ext = if irt then nfsd/6*5 else 0
   in ((px,py),(ex,ext),rta)

nextPQ :: Double -> Int -> Pos -> Pos
nextPQ cvH miq (p,q)
  | (fromIntegral q+1)*ht > cvH - cvT = (p-1,miq)
  | otherwise = (p,q+1)

rtChar :: Char -> Bool
rtChar ch = (cp>31 && cp<128)||(ch `elem` "ー〜。「＜＞（）") 
  where cp = fromEnum ch
