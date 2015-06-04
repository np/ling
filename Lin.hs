{-# LANGUAGE TemplateHaskell #-}
module Main where

import System.IO (stderr, hPutStrLn)
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Control.Monad (when)
import Control.Lens

import qualified MiniC.Print as C

import Lin.Lex (Token)
import Lin.Par
import Lin.Abs
import Lin.Print
import Lin.Reify
import Lin.Utils
import Lin.Print.Instances ()
import qualified Lin.Compile.C as Compile
import qualified Lin.Norm as N
import qualified Lin.Sequential as Sequential
import Lin.Proc.Checker (checkProgram)
import Lin.Term.Checker (runTC, debugChecker, CheckOpts, defaultCheckOpts)

import Lin.ErrM

type ParseFun a = [Token] -> Err a

data Opts = Opts { _tokens, _abstree, _lintree, _normtree, _check, _sequential
                 , _compile, _compilePrims, _noPrims :: Bool
                 , _checkOpts :: CheckOpts }

$(makeLenses ''Opts)

defaultOpts :: Opts
defaultOpts = Opts False False False False False False False False False defaultCheckOpts

prims :: String
prims = unlines
  ["Int   : Type."
  ,"_+_   : (m : Int)(n : Int) -> Int."
  ,"_-_   : (m : Int)(n : Int) -> Int."
  ,"_*_   : (m : Int)(n : Int) -> Int."
  ,"_/_   : (m : Int)(n : Int) -> Int."
  ,"_%_   : (m : Int)(n : Int) -> Int."
  ,"pow   : (m : Int)(n : Int) -> Int."
  ,"Vec   : (A : Type)(n : Int) -> Type."
  ,"take  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A m."
  ,"drop  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A n."
  ,"merge : (m : Int)(n : Int)(v0 : Vec Int m)(v1 : Vec Int n) -> Vec Int (m + n)."
  ,"sort  : (n : Int)(v : Vec Int n) -> Vec Int n."
  ,"Session : Type."
  ,"Double : Type."
  ,"Int2Double : (n : Int) -> Double."
  ,"_+D_ : (m : Double)(n : Double) -> Double."
  ,"_-D_ : (m : Double)(n : Double) -> Double."
  ,"_*D_ : (m : Double)(n : Double) -> Double."
  ,"_/D_ : (m : Double)(n : Double) -> Double."
  ,"powD : (m : Double)(n : Double) -> Double."
  ]

primsN :: [N.Dec]
primsN =
   case pListDec (myLexer prims) of
     Bad e -> error $ "Bad prims\n" ++ e
     Ok  t -> norm . reverse $ t

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
     Bad e    -> failIO $ "Parse Failed: " ++ e
     Ok  tree -> do showTree opts tree
                    return tree
  where ts = myLexer s

addPrims :: Bool -> N.Program -> N.Program
addPrims doAddPrims prg@(N.Program ds)
  | doAddPrims = N.Program (primsN ++ ds)
  | otherwise  = prg

failIO :: String -> IO a
failIO s = hPutStrLn stderr s >> exitFailure

runErr :: Err a -> IO a
runErr (Ok a)  = return a
runErr (Bad s) = failIO s

transP :: Opts -> Program -> IO ()
transP opts prg = do
  when (opts ^. normtree) $
    putStrLn (pretty nprg)
  when (opts ^. check) $ do
    runErr . runTC (opts ^. checkOpts) . checkProgram . addPrims (not(opts^.noPrims)) $ nprg
    putStrLn "Checking Sucessful!"
  when (opts ^. sequential) $
    putStrLn $ "\n{- Sequential process -}\n\n" ++ printTree sprg
  when (opts ^. compile) $
    putStrLn $ "\n/* Transformed tree */\n\n" ++ C.printTree cprg

  where nprg = norm prg
        sprg = Sequential.transProgram nprg
        cprg = Compile.transProgram (addPrims (opts^.compilePrims) sprg)

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
  "--compile-prims":args -> mainArgs (opts & compilePrims .~ True) args
  "--seq":args -> mainArgs (opts & sequential .~ True) args
  "--no-prims":args -> mainArgs (opts & noPrims .~ True) args
  arg@('-':'-':_:_):_ -> failIO $ "Unexpected argument " ++ arg
  [f] -> runProgram opts f
  fs  -> mapM_ (\f -> putStrLn f >> runProgram opts f) fs

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
