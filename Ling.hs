{-# LANGUAGE TemplateHaskell #-}
module Main where

import           System.Environment   (getArgs)
import           System.Exit          (exitFailure)
import           System.IO            (hPutStrLn, stderr)

import           Control.Lens
import           Control.Monad        (when)
import           Data.Monoid

import qualified MiniC.Print          as C

import           Ling.Abs
import           Ling.Check.Base      (TCOpts, debugChecker,
                                       defaultTCOpts, runTC)
import           Ling.Check.Program   (checkProgram)
import qualified Ling.Compile.C       as Compile
import           Ling.ErrM
import           Ling.Layout          (resolveLayout)
import           Ling.Lex             (Token)
import qualified Ling.Norm            as N
import           Ling.Par
import           Ling.Print
import           Ling.Reify
import qualified Ling.Sequential      as Sequential
import           Ling.Utils

type ParseFun a = [Token] -> Err a

data Opts = Opts { _tokens, _showAST, _showPretty, _doNorm, _check, _sequential
                 , _compile, _compilePrims, _noPrims :: Bool
                 , _checkOpts :: TCOpts }

$(makeLenses ''Opts)

defaultOpts :: Opts
defaultOpts = Opts False False False False False False False False False defaultTCOpts

debugCheck :: Setter' Opts Bool
-- debugCheck = mergeSetters check (checkOpts.debugChecker)
debugCheck = sets $ \f -> over (checkOpts.debugChecker) f . over check f

layoutLexer :: String -> [Token]
layoutLexer = resolveLayout True . myLexer

prims :: String
prims =
  "Int   : Type\n\
  \_+_   : (m : Int)(n : Int) -> Int\n\
  \_-_   : (m : Int)(n : Int) -> Int\n\
  \_*_   : (m : Int)(n : Int) -> Int\n\
  \_/_   : (m : Int)(n : Int) -> Int\n\
  \_%_   : (m : Int)(n : Int) -> Int\n\
  \pow   : (m : Int)(n : Int) -> Int\n\
  \Vec   : (A : Type)(n : Int) -> Type\n\
  \take  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A m\n\
  \drop  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A n\n\
  \merge : (m : Int)(n : Int)(v0 : Vec Int m)(v1 : Vec Int n) -> Vec Int (m + n)\n\
  \sort  : (n : Int)(v : Vec Int n) -> Vec Int n\n\
  \Session : Type\n\
  \Double : Type\n\
  \Int2Double : (n : Int) -> Double\n\
  \_+D_ : (m : Double)(n : Double) -> Double\n\
  \_-D_ : (m : Double)(n : Double) -> Double\n\
  \_*D_ : (m : Double)(n : Double) -> Double\n\
  \_/D_ : (m : Double)(n : Double) -> Double\n\
  \powD : (m : Double)(n : Double) -> Double\n\
  \Char : Type\n\
  \String : Type\n\
  \showInt : (n : Int) -> String\n\
  \showDouble : (n : Double) -> String\n\
  \showChar : (c : Char) -> String\n\
  \showString : (s : String) -> String\n\
  \_++S_ : (s0 : String)(s1 : String) -> String\n\
  \"

primsN :: N.Program
primsN =
   case pProgram (layoutLexer prims) of
     Bad e -> error $ "Bad prims\n" ++ e
     Ok  p -> norm p

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
  where ts = layoutLexer s

addPrims :: Bool -> Endom N.Program
addPrims doAddPrims
  | doAddPrims = (primsN <>)
  | otherwise  = id

failIO :: String -> IO a
failIO s = hPutStrLn stderr s >> exitFailure

runErr :: Err a -> IO a
runErr (Ok a)  = return a
runErr (Bad s) = failIO s

transP :: Opts -> Program -> IO ()
transP opts prg = do
  when (opts ^. doNorm) $
    putStrLn (pretty nprg)
  when (opts ^. check) $ do
    runErr . runTC (opts ^. checkOpts) . checkProgram . addPrims (not(opts^.noPrims)) $ nprg
    putStrLn "Checking Sucessful!"
  when (opts ^. sequential) $
    putStrLn $ "\n{- Sequential process -}\n\n" ++ pretty sprg
  when (opts ^. compile) $
    putStrLn $ "\n/* Transformed tree */\n\n" ++ C.printTree cprg

  where nprg = norm prg
        sprg = Sequential.transProgram nprg
        cprg = Compile.transProgram (addPrims (opts^.compilePrims) sprg)

showTree :: (Show a, Print a) => Opts -> a -> IO ()
showTree opts tree
 = do when (opts ^. showAST) $
        putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
      when (opts ^. showPretty) $
        putStrLn $ "\n-- Pretty-printed program\n\n" ++ pretty tree

mainArgs :: Opts -> [String] -> IO ()
mainArgs opts args0 = case args0 of
  [] -> getContents >>= run opts pProgram >>= transP opts
  ('-':'-':arg@(_:_)):args ->
    case arg of
      "tokens" -> add tokens
      "ast" -> add showAST
      "pretty" -> add showPretty
      "norm" -> add doNorm
      "check" -> add check
      "debug-check" -> add debugCheck
      "compile" -> add compile
      "compile-prims" -> add compilePrims
      "seq" -> add sequential
      "no-prims" -> add noPrims
      _ -> failIO $ "Unexpected flag --" ++ arg
    where add opt = mainArgs (opts & opt .~ True) args
  [f] -> runProgram opts f
  fs  -> mapM_ (\f -> putStrLn f >> runProgram opts f) fs

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
