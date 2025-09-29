{-# LANGUAGE OverloadedStrings #-}
module Convert where

import qualified Data.Text as T

import File (fileRead, fileWrite)

conv :: IO ()
conv = do
  lns <- T.lines . repText <$> fileRead inputFile
  lns2 <- T.lines . repText <$> fileRead inputFile2
  let res = "\nmodule Reki (rekiDoc, rekiDoc2) where\n\nrekiDoc :: String\nrekiDoc = \"" <> T.intercalate "\\n" lns <> "\"\n\nrekiDoc2 :: String\nrekiDoc2 = \"" <> T.intercalate "\\n" lns2 <> "\""
  fileWrite outputFile res

repText :: T.Text -> T.Text
repText = T.replace "」" ">" . T.replace "「" "<"

inputFile :: FilePath
inputFile = "Texts/reki.txt"

inputFile2 :: FilePath
inputFile2 = "Texts/reki2.txt"

outputFile :: FilePath
outputFile = "Reki.hs"
