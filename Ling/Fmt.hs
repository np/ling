import System.Environment ( getArgs )
import System.Exit ( exitFailure, exitSuccess )

import Ling.Fmt.Albert.ErrM
import Ling.Fmt.Albert.Par
import Ling.Fmt.Albert.Migrate

import Ling.Utils

runFile :: FilePath -> IO ()
runFile f = readFile f >>= run

run :: String -> IO ()
run s = let ts = myLexer s in case pProgram ts of
  Bad err  -> do putStrLn "\nParse              Failed...\n"
                 putStrLn err
                 exitFailure
  Ok  tree -> do putStrLn . pretty . transProgram $ tree
                 exitSuccess

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin."
    , "  (files)         Parse content of files."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run
    "-s":fs -> mapM_ runFile fs
    fs -> mapM_ runFile fs
