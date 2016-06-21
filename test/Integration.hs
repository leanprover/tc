module Integration where

import Test.Hspec
import Frontend.Parser

stdFilename = "data/all.out"
hottFilename = "data/all.hout"

test :: IO ()
test = do
  testStd
  testHott

testStd = do
  stdContents <- readFile stdFilename
  case typeCheckExportFile True stdFilename stdContents of
    Right _ -> return ()

testHott = do
  hottContents <- readFile hottFilename
  case typeCheckExportFile False hottFilename hottContents of
    Right _ -> return ()
