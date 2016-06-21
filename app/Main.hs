module Main where

import Frontend.Parser

import System.Environment
import Data.List (isSuffixOf)

printUsage = putStrLn "usage: leantc <filename>.[h]out"

main = do
  args <- getArgs
  case args of
    [] -> printUsage
    (_:_:_) -> printUsage
    [filename] -> do
      let useStd = isSuffixOf ".out" filename
      let useHott = isSuffixOf ".hout" filename
      if useStd || useHott
      then do
        fileContents <- readFile filename
        case typeCheckExportFile useStd filename fileContents of
          Left err -> putStrLn err
          Right _ -> putStrLn "Congratulations!"
      else printUsage
