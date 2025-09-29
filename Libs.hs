module Libs where

import Data.Time.Clock(getCurrentTime,UTCTime(utctDayTime))

isChar :: String -> Bool
isChar = foldr (\x -> (&&) (x `elem` ['a'..'z']++['A'..'Z'])) True

isNum :: String -> Bool
isNum = foldr (\x -> (&&) (x `elem` "0123456789+-")) True

getIndex :: Eq a => a -> [a] -> Int
getIndex _ [] = 0
getIndex t (x:xs) = if t==x then 0 else 1+ getIndex t xs

sepByChar :: Char -> String -> [String]
sepByChar _ [] = [[]]
sepByChar _ [x] = [[x]]
sepByChar ch (x:xs)
  | ch==x = []:(hd:tl)
  | otherwise = (x:hd):tl
  where (hd:tl) = sepByChar ch xs

getInside :: Char -> Int -> String -> String
getInside ch mc msg = drop (mc+1) (getToChar ch (mc+1) msg) 
  where getToChar _ _ [] = []
        getToChar ch mc msg
          | msg!!mc==ch = take mc msg
          | otherwise = getToChar ch (mc+1) msg

concatWith :: Char -> [String] -> String
concatWith ch lst = init$concatMap (++[ch]) lst

-- get random number(Int) from 0 to (i-1)
-- input (Number,Generator) -> output (Number,Generator)
getRandomNumIO :: (Int,Int) -> IO (Int,Int)
getRandomNumIO (i,g) = do
  utime <- getCurrentTime 
  let time = show (utctDayTime utime)
  let ntime = init time
  let n = (read$last$sepByChar '.' ntime)::Int
  let ng = (read$take 3 (show (n+g*(i-1))))::Int
  let m = mod ng i
  return (m,ng)

getRandomNum :: (Int,Int) -> (Int,Int)
getRandomNum (i,g) =
  let ng = (read$take 3 (show (g*(i-1))))::Int
      m = mod ng i
   in (m,ng)

--
