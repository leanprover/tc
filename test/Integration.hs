module Integration where

import Test.Hspec
import Frontend.Parser

stdFilename = "data/all.out"

test :: IO ()
test = do
  testStd

testStd = do
  stdContents <- readFile stdFilename
  case typeCheckExportFile stdFilename stdContents of
    Right _ -> return ()

