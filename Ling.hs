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
import           Ling.Fuse          (fuseProgram)
import           Ling.Reify
import qualified Ling.Sequential    as Sequential

type ParseFun a = [Token] -> Err a

data Opts =
       Opts
         { _tokens,_showAST,_showPretty,_doNorm,_check,_sequential,_fuse,_compile,_compilePrims,_noPrims :: Bool
         , _checkOpts                                                                              :: TCOpts
         }

$(makeLenses ''Opts)

defaultOpts :: Opts
defaultOpts = Opts False False False False False False False False False False defaultTCOpts

debugCheck :: Setter' Opts Bool
debugCheck = mergeSetters check (checkOpts.debugChecker)

layoutLexer :: String -> [Token]
layoutLexer = resolveLayout True . myLexer

prims :: String
prims = [q|
data Empty =
data Unit = `unit
data Bool = `false | `true
not : (x : Bool)-> Bool
    = \(x : Bool)-> case x of { `false -> `true, `true -> `false }
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
Allocation : Type
auto : Allocation
fused : Allocation
fuse : (depth : Int)-> Allocation
alloc : Allocation = fuse 0
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
    for_ ts cpprint
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
    putStrLn $ "\n{- Sequential program -}\n\n" ++ pretty sprg
  when (opts ^. fuse) $
    putStrLn $ "\n{- Fused program -}\n\n" ++ pretty fprg
  when (opts ^. compile) $
    putStrLn $ "\n/* C program */\n\n" ++ C.printTree cprg

  where
    nprg = norm prg
    sprg = Sequential.transProgram nprg
    fprg = fuseProgram sprg
    cprg = Compile.transProgram (addPrims (opts ^. compilePrims) sprg)

showTree :: (Show a, Print a) => Opts -> a -> IO ()
showTree opts tree = do
  when (opts ^. showAST) $ do
    putStrLn "\n[Abstract Syntax]\n\n"
    cpprint tree
  when (opts ^. showPretty) $
    putStrLn $ "\n-- Pretty-printed program\n\n" ++ pretty tree

flagSpec :: [(String, (Endom Opts, String))]
flagSpec =
  (\(x,y,z) -> (x,(y,z))) <$>
  [ ("check"        , add check                   , "Type check the program")
  , ("compile"      , add compile                 , "Display the compiled program (C language)")
  , ("pretty"       , add showPretty              , "Display the program")
  , ("norm"         , add doNorm                  , "Display the normalized program")
  , ("fuse"         , add fuse                    , "Display the fused program")
  , ("seq"          , add sequential              , "Display the sequential program")
  , ("tokens"       , add tokens                  , "Display the program as a list of tokens from the lexer")
  , ("ast"          , add showAST                 , "Display the program as an Abstract Syntax Tree")
  , ("debug-check"  , add debugCheck              , "Display debugging information while checking")
  , ("compile-prims", add compilePrims            , "Also compile the primitive definitions")
  , ("strict-par"   , add (checkOpts . strictPar) , "Make the checker stricter about pars (no mix rule)")
  , ("no-prims"     , add noPrims                 , "Do not include the primitive definitions")
  ] where add opt opts = opts & opt .~ True

usage :: String -> IO a
usage msg = failIO $ unlines (msg : "" : "Usage: Ling [option...] [file...]" : "" : "option ::=" : (fmtFlag <$> flagSpec))
  where
    fmtFlag (flag, (_, desc)) = "  | --" ++ pad flag ++ " # " ++ desc
    Just maxlen = maximumOf (each . _1 . to length) flagSpec
    pad s = take maxlen (s ++ repeat ' ')

mainArgs :: Opts -> [String] -> IO ()
mainArgs opts = \case
  [] -> getContents >>= run opts pProgram >>= transP opts
  ("--help":_) -> usage ""
  ('-':'-':arg@(_:_)):args ->
    case lookup arg flagSpec of
      Just (opt, _) -> mainArgs (opt opts) args
      _             -> usage $ "Unexpected flag --" ++ arg
  [f] -> runProgram opts f
  fs  -> for_ fs $ \f -> putStrLn f >> runProgram opts f

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
