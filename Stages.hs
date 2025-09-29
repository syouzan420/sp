module Stages(stages,evts,players,initPos,gridSize,idef) where

import Define (Stage,Evt,Size,Pos,Def,Mode(..))

map0 :: Stage
map0 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr))]

map1 :: Stage
map1 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr))]

map2 :: Stage
map2 = [((1,0),('D',Bl)),((4,1),('A',Bl)),((0,3),('C',Bl)),((2,5),('B',Bl)),((4,5),('n',Ex))]

map3 :: Stage
map3 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr)),((6,4),('d',Fr))]

map4 :: Stage
map4 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr)),((6,4),('d',Fr))]

map5 :: Stage
map5 = [((1,0),('G',Bl)),((4,1),('E',Bl)),((0,3),('H',Bl)),((2,5),('F',Bl)),((4,5),('n',Ex))]

map6 :: Stage
map6 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((4,2),('e',Fr)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr)),((6,4),('d',Fr))]

map7 :: Stage
map7 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((4,2),('e',Fr)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr)),((6,4),('d',Fr))]

map8 :: Stage
map8 = [((2,0),('I',Bl))]

stages :: [Stage]
stages = [map0,map1,map2,map3,map4,map5,map6,map7,map8]

evts :: [Evt]
evts = []

players :: [Char]
players = "@@@@@@@@@"

initPos :: [Pos]
initPos = [(2,2),(2,2),(2,2),(2,2),(2,2),(2,2),(2,2),(2,2),(2,2)]

gridSize :: [Size]
gridSize = [(5,5),(5,5),(5,6),(7,5),(7,5),(5,6),(7,5),(7,5),(5,6)]

idef :: [(Def,Int)]
idef = []