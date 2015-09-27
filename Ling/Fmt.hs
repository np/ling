import           System.Environment      (getArgs)
import           System.Exit             (exitFailure)
import           System.IO

import           Ling.Fmt.Albert.ErrM
import           Ling.Fmt.Albert.Layout
import           Ling.Fmt.Albert.Migrate
import           Ling.Fmt.Albert.Par

import           Ling.Print

runFile :: FilePath -> IO ()
runFile f = hPutStrLn stderr f >> readFile f >>= run

run :: String -> IO ()
run s = let ts = resolveLayout True $ myLexer s in case pProgram ts of
  Bad err  -> do putStrLn "\nParse              Failed...\n"
                 putStrLn err
                 exitFailure
  Ok  tree -> putStrLn . printTree . transProgram $ tree

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
