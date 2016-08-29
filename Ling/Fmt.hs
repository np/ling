module Ling.Fmt where
import           System.Environment      (getArgs)
import           System.Exit             (exitFailure)
import           System.IO

import           Ling.ErrM

import           Ling.Fmt.Albert.Abs       as A
import           Ling.Fmt.Albert.Layout    as A
import           Ling.Fmt.Albert.Migrate   as A
import           Ling.Fmt.Albert.Par       as A

import           Ling.Fmt.Benjamin.Abs     as B
import           Ling.Fmt.Benjamin.Layout  as B
import           Ling.Fmt.Benjamin.Migrate as B
import           Ling.Fmt.Benjamin.Par     as B

import           Ling.Print
import           Ling.Prelude

runFile :: FilePath -> IO ()
runFile f = hPutStrLn stderr f >> readFile f >>= run

parseA :: String -> Err A.Program
parseA = A.pProgram . A.resolveLayout True . A.myLexer

parseB :: String -> Err B.Program
parseB = B.pProgram . B.resolveLayout True . B.myLexer

(<<|>>) :: Err a -> Err a -> Err a
Ok tree  <<|>> _        = Ok tree
_        <<|>> Ok tree  = Ok tree
Bad err0 <<|>> Bad err1 = Bad (err0 <> "\n\n" <> err1)

run :: String -> IO ()
run s = case  (B.transProgram <$> parseB s)
        <<|>> (B.transProgram . A.transProgram <$> parseA s) of
  Bad err  -> do putStrLn "\nParse              Failed...\n"
                 putStrLn err
                 exitFailure
  Ok  tree -> putStrLn . pretty $ tree

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
    "-s":fs -> for_ fs runFile
    fs -> for_ fs runFile
