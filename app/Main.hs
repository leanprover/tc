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
        fileContents <- readFile filename
        case typeCheckExportFile filename fileContents of
          Left err -> putStrLn err
          Right _ -> putStrLn "Congratulations!"
