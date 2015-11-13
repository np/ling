{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import           System.Environment (getArgs)
import           System.Exit        (exitFailure)
import           System.IO          (hPutStrLn, stderr)

import           IPPrint.Colored

import qualified MiniC.Print        as C

import           Ling.Abs
import           Ling.Check.Base    (TCOpts, debugChecker, defaultTCOpts, runTC,
                                     strictPar)
import           Ling.Check.Program (checkProgram)
import qualified Ling.Compile.C     as Compile
import           Ling.ErrM
import           Ling.Layout        (resolveLayout)
import           Ling.Lex           (Token)
import qualified Ling.Norm          as N
import           Ling.Par
import           Ling.Prelude
import           Ling.Print
import           Ling.Reify
import qualified Ling.Sequential    as Sequential

type ParseFun a = [Token] -> Err a

data Opts =
       Opts
         { _tokens,_showAST,_showPretty,_doNorm,_check,_sequential,_compile,_compilePrims,_noPrims :: Bool
         , _checkOpts                                                                              :: TCOpts
         }

$(makeLenses ''Opts)

defaultOpts :: Opts
defaultOpts = Opts False False False False False False False False False defaultTCOpts

debugCheck :: Setter' Opts Bool
-- debugCheck = mergeSetters check (checkOpts.debugChecker)
debugCheck = sets $ \f -> over (checkOpts . debugChecker) f . over check f

layoutLexer :: String -> [Token]
layoutLexer = resolveLayout True . myLexer

prims :: String
prims = [q|
data Empty =
data Unit = `unit
data Bool = `false | `true
data LR = `left | `right
Int   : Type
_+_   : (m : Int)(n : Int) -> Int
_-_   : (m : Int)(n : Int) -> Int
_*_   : (m : Int)(n : Int) -> Int
_/_   : (m : Int)(n : Int) -> Int
_%_   : (m : Int)(n : Int) -> Int
pow   : (m : Int)(n : Int) -> Int
Vec   : (A : Type)(n : Int) -> Type
take  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A m
drop  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A n
merge : (m : Int)(n : Int)(v0 : Vec Int m)(v1 : Vec Int n) -> Vec Int (m + n)
sort  : (n : Int)(v : Vec Int n) -> Vec Int n
Session : Type
IO = \(I : Type)(O : (i : I) -> Type)-> ?(x : I). !O x
IO' = \(I : Type)(O : Type)-> ?I. !O
Par = \(S0 : Session)(S1 : Session)-> {S0, S1}
Ten = \(S0 : Session)(S1 : Session)-> [S0, S1]
Seq = \(S0 : Session)(S1 : Session)-> [:S0, S1:]
ParIO = \(I : Type)(O : Type)-> {?I, !O}
TenIO = \(I : Type)(O : Type)-> [?I, !O]
TenOI = \(O : Type)(I : Type)-> [!O, ?I]
SeqIO = \(I : Type)(O : Type)-> [: ?I, !O :]
SeqOI = \(O : Type)(I : Type)-> [: !O, ?I :]
EndoIO = \(T : Type)-> IO' T T
EndoLoli = \(S : Session)-> S -o S
EndoParIO = \(T : Type)-> ParIO T T
EndoTenIO = \(T : Type)-> TenIO T T
EndoTenOI = \(T : Type)-> TenOI T T
EndoSeqIO = \(T : Type)-> SeqIO T T
DotSort = \(A : Type)(n : Int)-> EndoIO (Vec A n)
ParSort = \(A : Type)(n : Int)-> EndoLoli (!Vec A n)
SeqSort = \(A : Type)(n : Int)-> [: ?Vec A n, !Vec A n :]
Double : Type
Int2Double : (n : Int) -> Double
_+D_ : (m : Double)(n : Double) -> Double
_-D_ : (m : Double)(n : Double) -> Double
_*D_ : (m : Double)(n : Double) -> Double
_/D_ : (m : Double)(n : Double) -> Double
powD : (m : Double)(n : Double) -> Double
Char : Type
String : Type
showInt : (n : Int) -> String
showDouble : (n : Double) -> String
showChar : (c : Char) -> String
showString : (s : String) -> String
_++S_ : (s0 : String)(s1 : String) -> String
|]

primsN :: N.Program
primsN =
  case pProgram (layoutLexer prims) of
    Bad e -> error $ "Bad prims\n" ++ e
    Ok p  -> norm p

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
    Bad e -> failIO $ "Parse Failed: " ++ e
    Ok tree -> do
      showTree opts tree
      return tree

  where
    ts = layoutLexer s

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
    runErr . runTC (opts ^. checkOpts) . checkProgram . addPrims (not (opts ^. noPrims)) $ nprg
    putStrLn "Checking Sucessful!"
  when (opts ^. sequential) $
    putStrLn $ "\n{- Sequential process -}\n\n" ++ pretty sprg
  when (opts ^. compile) $
    putStrLn $ "\n/* Transformed tree */\n\n" ++ C.printTree cprg

  where
    nprg = norm prg
    sprg = Sequential.transProgram nprg
    cprg = Compile.transProgram (addPrims (opts ^. compilePrims) sprg)

showTree :: (Show a, Print a) => Opts -> a -> IO ()
showTree opts tree = do
  when (opts ^. showAST) $ do
    putStrLn "\n[Abstract Syntax]\n\n"
    cpprint tree
  when (opts ^. showPretty) $
    putStrLn $ "\n-- Pretty-printed program\n\n" ++ pretty tree

mainArgs :: Opts -> [String] -> IO ()
mainArgs opts = \case
  [] -> getContents >>= run opts pProgram >>= transP opts
  ('-':'-':arg@(_:_)):args ->
    case arg of
      "tokens"        -> add tokens
      "ast"           -> add showAST
      "pretty"        -> add showPretty
      "norm"          -> add doNorm
      "check"         -> add check
      "debug-check"   -> add debugCheck
      "compile"       -> add compile
      "compile-prims" -> add compilePrims
      "strict-par"    -> add (checkOpts . strictPar)
      "seq"           -> add sequential
      "no-prims"      -> add noPrims
      _               -> failIO $ "Unexpected flag --" ++ arg
    where add opt = mainArgs (opts & opt .~ True) args
  [f] -> runProgram opts f
  fs  -> for_ fs $ \f -> putStrLn f >> runProgram opts f

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
