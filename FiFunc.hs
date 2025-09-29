module FiFunc(funcPon,stagePon,doNothing) where

import Data.Char(isDigit)
import Define (Size,Pos,Def,Fpon,Spon,Mode(..))
--funcPon :: [Fpon]
--funcPon = [('@',id),('A',addone),('S',subone)]

funcPon :: [Fpon]
funcPon = [('@',id)]

stagePon :: [Spon]
stagePon = [(5,makeShift)]

addone :: Char -> Char
addone = makeNext 1

subone :: Char -> Char
subone = makeNext (-1)

makeNext :: Int -> Char -> Char
makeNext i ch
  |isDigit ch = let tn = (read [ch]::Int)+i
                    res
                      |tn==10 = '9'
                      |tn==(-1) = '0'
                      |otherwise = last$show tn
                 in res 
  |otherwise = let en = fromEnum ch
                   en' = en+i
                   nen
                     |en'>122 = 97+(en'-122)
                     |en'<97 && en'>90 = 65+(en'-90)
                     |otherwise = en'
                   tc = toEnum nen::Char
                in if tc `elem` map fst funcPon
                      then makeNext i tc
                      else tc

makeShift :: Char -> Char -> Char
makeShift ic ch = if isDigit ic then makeNext (read [ic]) ch
                                else ch

doNothing :: Char -> Char -> Char
doNothing _ ch = ch

