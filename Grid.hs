module Grid (intoGrid,fromGrid,sizeGrid,checkGrid,makeGrid,toSee,toHide,
             changeGridType,clFromGrid,posGrid) where

import Define (Pos,Cell,Stage,Size,Grid,Mode(..))

intoGrid :: Pos -> Cell -> Grid -> Grid
intoGrid (x,y) (ch,tp) grid =
  let gline = grid!!y
      ngline = take x gline ++ [(ch,tp)] ++ drop (x+1) gline
   in take y grid ++ [ngline] ++ drop (y+1) grid

fromGrid :: Pos -> Grid -> Cell
fromGrid (x,y) grid = (grid!!y)!!x

posGrid :: Cell -> Grid -> Pos
posGrid _ [] = (0,0) 
posGrid cel (y:ys)
  | cel `elem` y = (posxGrid cel y,0)
  | otherwise = (fst$posGrid cel ys, 1 + snd (posGrid cel ys))
  where posxGrid _ [] = 0 
        posxGrid cl (x:xs)
          | cl==x = 0
          | otherwise = 1 + posxGrid cl xs

sizeGrid :: Grid -> Size
sizeGrid grid =
  let gline0 = head grid 
   in (length gline0, length grid)

checkGrid :: Cell -> Grid -> Bool
checkGrid _ [] = False
checkGrid (sch,stp) ([(ch,tp)]:ys) =
  if sch==' ' then (stp==tp)||cg2 else (sch==ch && stp==tp)||cg2
                 where cg2 = checkGrid (sch,stp) ys
checkGrid (sch,stp) (((ch,tp):xs):ys) =
  if sch==' ' then (stp==tp)||cg1 
              else (sch==ch && stp==tp)||cg1
                 where cg1 = checkGrid (sch,stp) (xs:ys)

changeGridType :: Cell -> Grid -> Grid
changeGridType _ [] = []
changeGridType (ch,tp) (g:gs) =
  let (chs,tps) = unzip g 
      ids = getIndexList ch chs
      ntps = changeList tp ids tps
   in zip chs ntps:changeGridType (ch,tp) gs

clFromGrid :: Char -> Grid -> Grid
clFromGrid _ [] = []
clFromGrid ch (g:gs) =
  let (chs,tps) = unzip g
      ids = getIndexList ch chs
      nchs = changeList ' ' ids chs
      ntps = changeList Fr ids tps
   in zip nchs ntps:clFromGrid ch gs

getIndexList :: Char -> String -> [Int]
getIndexList ch chs = indexList 0 ch chs
  where indexList _ _ [] = []
        indexList i ch (x:xs) = if ch==x then i:indexList (i+1) ch xs
                                         else indexList (i+1) ch xs

changeList :: a -> [Int] -> [a] -> [a]
changeList e ids lst = cList 0 e ids lst
  where cList _ _ _ [] = []
        cList i e ids (x:xs) = if i `elem` ids then e:cList (i+1) e ids xs
                                               else x:cList (i+1) e ids xs

makeGrid :: Size -> Stage -> Grid
makeGrid (wd,hi) sta =
  flatToGrid wd $
    [(\(x,y) -> findxy (x,y) sta) (x,y)|y<-[0..(hi-1)],x<-[0..(wd-1)]]
    where findxy _ [] = (' ',Fr) 
          findxy (a,b) (((p,q),scell):xs) =
                  if a==p&&b==q then scell else findxy (a,b) xs 

flatToGrid :: Int -> [a] -> [[a]]
flatToGrid _ [] = []
flatToGrid wd ls = take wd ls:flatToGrid wd (drop wd ls)

toSee :: Grid -> Grid
toSee [] = []
toSee (l:ls) = toSeeLine l:toSee ls
  where toSeeLine [] = []
        toSeeLine ((ch,tp):xs)
          |ch/=' ' && tp==DF = (ch,Fr):toSeeLine xs
          |ch/=' ' && tp==DB = (ch,Bl):toSeeLine xs
          |otherwise = (ch,tp):toSeeLine xs

toHide :: Grid -> Grid
toHide [] = []
toHide (l:ls) = toHideLine l:toHide ls
  where toHideLine [] = []
        toHideLine ((ch,tp):xs)
          |ch/=' ' && tp==Fr = (ch,DF):toHideLine xs
          |ch/=' ' && tp==Bl = (ch,DB):toHideLine xs
          |otherwise = (ch,tp):toHideLine xs

