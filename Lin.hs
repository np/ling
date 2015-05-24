{-# LANGUAGE TemplateHaskell #-}
module Main where

import System.IO ( stderr, hPutStrLn )
import System.Environment ( getArgs )
import System.Exit ( exitFailure )
import Control.Lens
import Control.Monad (when)

import Lin.Lex (Token)
import Lin.Par
import Lin.Abs
import Lin.Print

import qualified MiniCXX.Print as C

import Lin.Reify
import Lin.Utils
import Lin.Print.Instances ()
import Lin.Compile.CXX
import qualified Lin.Norm as N
import Lin.Proc.Checker (checkProgram)
import Lin.Term.Checker (runTC, debugChecker, CheckOpts, defaultCheckOpts)

import Lin.ErrM

type ParseFun a = [Token] -> Err a

myLLexer :: String -> [Token]
myLLexer = myLexer

type Verbosity = Int

data Opts = Opts { _tokens, _abstree, _lintree, _normtree, _check, _compile :: Bool
                 , _checkOpts :: CheckOpts }

$(makeLenses ''Opts)

defaultOpts :: Opts
defaultOpts = Opts False False False False False False defaultCheckOpts

putStrV :: Verbosity -> String -> IO ()
putStrV v = when (v > 1) . putStrLn

prims :: String
prims = unlines
  ["-- begin prims"
  ,"Int   : Type."
  ,"_+_   : (m : Int)(n : Int) -> Int."
  ,"Vec   : (A : Type)(n : Int) -> Type."
  ,"take  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A m."
  ,"drop  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A n."
  ,"merge : (m : Int)(n : Int)(v0 : Vec Int m)(v1 : Vec Int n) -> Vec Int (m + n)."
  ,"sort  : (n : Int)(v : Vec Int n) -> Vec Int n."
  ,"-- end prims"
  ]

primsN :: [N.Dec]
primsN =
   case pListDec (myLLexer prims) of
     Bad e -> error $ "Bad prims\n" ++ e
     Ok  t -> norm t

runFile :: (Print a, Show a) => Opts -> ParseFun a -> FilePath -> IO a
runFile v p f = readFile f >>= run v p

runProgram :: Opts -> FilePath -> IO ()
runProgram opts f = runFile opts pProgram f >>= transP opts

run :: (Print a, Show a) => Opts -> ParseFun a -> String -> IO a
run opts p s = do
   when (opts ^. tokens) $ do
     putStrLn "Tokens:"
     print ts
   case p ts of
     Bad e    -> do putStrLn "\nParse              Failed...\n"
                    putStrLn e
                    exitFailure
     Ok  tree -> do showTree opts tree
                    return tree
  where ts = myLLexer s

addPrims :: N.Program -> N.Program
addPrims (N.Program ds) = N.Program (primsN ++ ds)

runErr :: Err a -> IO a
runErr (Ok a)  = return a
runErr (Bad s) = do hPutStrLn stderr s
                    exitFailure

transP :: Opts -> Program -> IO ()
transP opts prg = do
  when (opts ^. normtree) $
    putStrLn (pretty nprg)
  when (opts ^. check) $ do
    runErr . runTC (opts ^. checkOpts) . checkProgram . addPrims $ nprg
    putStrLn "Checking Sucessful!"
  when (opts ^. compile) $
    putStrLn $ "\n[Transformed tree]\n\n" ++ C.printTree tree

  where nprg = norm prg
        tree = transProgram nprg

showTree :: (Show a, Print a) => Opts -> a -> IO ()
showTree opts tree
 = do when (opts ^. abstree) $
        putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
      when (opts ^. lintree) $
        putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

mainArgs :: Opts -> [String] -> IO ()
mainArgs opts args0 = case args0 of
  [] -> getContents >>= run opts pProgram >>= transP opts
  "--tokens":args -> mainArgs (opts & tokens .~ True) args
  "--abstree":args -> mainArgs (opts & abstree .~ True) args
  "--lintree":args -> mainArgs (opts & lintree .~ True) args
  "--normtree":args -> mainArgs (opts & normtree .~ True) args
  "--check":args -> mainArgs (opts & check .~ True) args
  "--debug-check":args -> mainArgs (opts & check .~ True & checkOpts . debugChecker .~ True) args
  "--compile":args -> mainArgs (opts & compile .~ True) args
  [f] -> runProgram opts f
  fs  -> mapM_ (\f -> putStrLn f >> runProgram opts f) fs

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
