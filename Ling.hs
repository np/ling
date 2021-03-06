{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}

module Ling where

import           Control.Monad.Writer (tell, execWriter)

import           Data.Char (isDigit)

import           System.Environment (getArgs)
import           System.Exit        (exitFailure)
import           System.IO          (hPutStrLn, stderr)

import qualified MiniC.Print        as C

import           Ling.Abs
import           Ling.Check.Base    ( TCEnv, TCOpts, debugChecker, defaultTCOpts, runTCOpts
                                    , runTCEnv, strictPar, edefs, errorScope, tcOpts)
import           Ling.Check.Program (checkProgram)
import qualified Ling.Compile.C     as Compile
import           Ling.Defs          (reduceL)
import           Ling.ErrM
import           Ling.Layout        (resolveLayout)
import           Ling.Lex           (Token)
import qualified Ling.Norm          as N
import           Ling.Norm          (transProgramDecs)
import           Ling.Par
import           Ling.Prelude
import           Ling.Print
import           Ling.Fuse          (fuseProgram)
import           Ling.Scoped        (Scoped(Scoped))
import           Ling.Subst         (substDefs)
import           Ling.SubTerms      (transProgramTerms)
import           Ling.Reify
import           Ling.Rename        (hDec)
import qualified Ling.Sequential    as Sequential

type ParseFun a = [Token] -> Err a

data Opts =
       Opts
         { _noCheck, _showExpand, _doExpand, _doReduce, _doSeq
         , _noSequential,  _showTokens, _showAST, _showPretty, _noNorm
         , _doRefresh, _doFuse, _compile, _compilePrims, _noPrims   :: Bool
         , _checkOpts :: TCOpts
         , _seqGas :: Int
         }

$(makeLenses ''Opts)

check :: Lens' Opts Bool
check = noCheck . iso not not

defaultOpts :: Opts
defaultOpts = Opts False False False False False False False False False False
                   False False False False False defaultTCOpts maxBound

debugCheck :: Setter' Opts Bool
debugCheck = mergeSetters check (checkOpts.debugChecker)

layoutLexer :: String -> [Token]
layoutLexer = resolveLayout True . myLexer

prims :: String
prims = [q|
id  :  (A : Type)(x : A)-> A
    = \(A : Type)(x : A)-> x
_:_ :  (A : Type)(x : A)-> A
    = \(A : Type)(x : A)-> x
data Empty =
data Unit = `unit
data Bool = `false | `true
not   : (x   : Bool)-> Bool = \(x   : Bool)-> case x of { `false -> `true, `true -> `false }
_&&_  : (x y : Bool)-> Bool = \(x y : Bool)-> case x of { `false -> `false, `true -> y }
_||_  : (x y : Bool)-> Bool = \(x y : Bool)-> case x of { `false -> y, `true -> `true }
_==B_ : (x y : Bool)-> Bool = \(x y : Bool)-> case x of { `false -> not y, `true -> y }
_/=B_ : (x y : Bool)-> Bool = \(x y : Bool)-> case x of { `false -> y, `true -> not y }
data LR = `left | `right
Int   : Type
_+_   : (m : Int)(n : Int) -> Int
_-_   : (m : Int)(n : Int) -> Int
_*_   : (m : Int)(n : Int) -> Int
_/_   : (m : Int)(n : Int) -> Int
_%_   : (m : Int)(n : Int) -> Int
pow   : (m : Int)(n : Int) -> Int
_==I_ : (m : Int)(n : Int) -> Bool
_<=I_ : (m : Int)(n : Int) -> Bool
_>=I_ : (m : Int)(n : Int) -> Bool
_<I_ : (m : Int)(n : Int) -> Bool
_>I_ : (m : Int)(n : Int) -> Bool
Vec   : (A : Type)(n : Int) -> Type
take  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A m
drop  : (A : Type)(m : Int)(n : Int)(v : Vec A (m + n)) -> Vec A n
merge : (m : Int)(n : Int)(v0 : Vec Int m)(v1 : Vec Int n) -> Vec Int (m + n)
sort  : (n : Int)(v : Vec Int n) -> Vec Int n
Session : Type
Log  : (S : Session)-> Session
Seq  : (S : Session)-> Session
Send : (S : Session)-> Session
Recv : (S : Session)-> Session
IO = \(I : Type)(O : (i : I) -> Type)-> ?(x : I). !O x
IO' = \(I : Type)(O : Type)-> ?I. !O
Par2 = \(S0 : Session)(S1 : Session)-> {S0, S1}
Ten2 = \(S0 : Session)(S1 : Session)-> [S0, S1]
Seq2 = \(S0 : Session)(S1 : Session)-> [:S0, S1:]
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
With = \(SL SR : Session)-> ?(b : LR). (case b of { `left -> SL, `right -> SR })
Oplus = \(SL SR : Session)-> !(b : LR). (case b of { `left -> SL, `right -> SR })
with_ =
  \(SL SR : Session)
   (pL : < SL >)(pR : < SR >)->
  proc(c : With SL SR)
    let x : LR <- c.
    @(case x of { `left -> pL, `right -> pR })(c)
oplus =
  \(SL SR : Session)
   (b : LR)
   (p : < case b of { `left -> SL, `right -> SR } >)->
  proc(c)
    c : Oplus SL SR <- b.
    @p(c)
receiver =
  \(A : Type)
   (S : A -> Session)
   (p : (x : A)-> < S x >)->
  proc(c)
    let x : A <- c.
    @(p x)(c)
sender =
  \(A : Type)
   (S : A -> Session)
   (t : A)
   (p : < S t >)->
  proc(c)
    c : !(x : A). S x <- t.
    @p(c)
Allocation : Type
auto : Allocation
fused : Allocation
fuse : (depth : Int)-> Allocation
alloc : Allocation = fuse 0
fuse1 : Allocation = fuse 1
fuse2 : Allocation = fuse 2
fuse3 : Allocation = fuse 3
Double : Type
_+D_ : (m : Double)(n : Double) -> Double
_-D_ : (m : Double)(n : Double) -> Double
_*D_ : (m : Double)(n : Double) -> Double
_/D_ : (m : Double)(n : Double) -> Double
powD : (m : Double)(n : Double) -> Double
_==D_ : (m : Double)(n : Double) -> Bool
_<=D_ : (m : Double)(n : Double) -> Bool
_>=D_ : (m : Double)(n : Double) -> Bool
_<D_ : (m : Double)(n : Double) -> Bool
_>D_ : (m : Double)(n : Double) -> Bool
Char : Type
_==C_ : (c0 c1 : Char)-> Bool
_>=C_ : (c0 c1 : Char)-> Bool
_<=C_ : (c0 c1 : Char)-> Bool
_>C_ : (c0 c1 : Char)-> Bool
_<C_ : (c0 c1 : Char)-> Bool
String : Type
_==S_ : (s0 s1 : String)-> Bool
showInt : (n : Int) -> String
showDouble : (n : Double) -> String
showChar : (c : Char) -> String
showString : (s : String) -> String
_++S_ : (s0 : String)(s1 : String) -> String
ccall : (A : Type)-> String -> A
Int2Double = ccall (Int -> Double) "(double)"
Int2Char = ccall (Int -> Char) "(char)"
sqrtD = ccall (Double -> Double) "sqrt"
ctype : String -> Type
cconst : (A : Type)-> String -> A
-- math.h
PI = cconst Double "M_PI"

-- complex.h
ComplexDouble : Type = ctype "complex double"
ComplexI = cconst ComplexDouble "_Complex_I"
Int2ComplexDouble = ccall (Int -> ComplexDouble) "(double complex)"
Double2Complex = ccall (Double -> ComplexDouble) "(double complex)"
_+CD_ : (m : ComplexDouble)(n : ComplexDouble) -> ComplexDouble
_-CD_ : (m : ComplexDouble)(n : ComplexDouble) -> ComplexDouble
_*CD_ : (m : ComplexDouble)(n : ComplexDouble) -> ComplexDouble
_/CD_ : (m : ComplexDouble)(n : ComplexDouble) -> ComplexDouble
powCD : (m : ComplexDouble)(n : ComplexDouble) -> ComplexDouble
_==CD_ : (m : ComplexDouble)(n : ComplexDouble) -> Bool
_<=CD_ : (m : ComplexDouble)(n : ComplexDouble) -> Bool
_>=CD_ : (m : ComplexDouble)(n : ComplexDouble) -> Bool
_<CD_ : (m : ComplexDouble)(n : ComplexDouble) -> Bool
_>CD_ : (m : ComplexDouble)(n : ComplexDouble) -> Bool
cabs = ccall (ComplexDouble -> Double) "cabs"
cacos = ccall (ComplexDouble -> ComplexDouble) "cacos"
cacosh = ccall (ComplexDouble -> ComplexDouble) "cacosh"
carg = ccall (ComplexDouble -> ComplexDouble) "carg"
casin = ccall (ComplexDouble -> ComplexDouble) "casin"
casinh = ccall (ComplexDouble -> ComplexDouble) "casinh"
catan = ccall (ComplexDouble -> ComplexDouble) "catan"
catanh = ccall (ComplexDouble -> ComplexDouble) "catanh"
ccos = ccall (ComplexDouble -> ComplexDouble) "ccos"
ccosh = ccall (ComplexDouble -> ComplexDouble) "ccosh"
cexp = ccall (ComplexDouble -> ComplexDouble) "cexp"
cimag = ccall (ComplexDouble -> Double) "cimag"
clog = ccall (ComplexDouble -> ComplexDouble) "clog"
conj = ccall (ComplexDouble -> ComplexDouble) "conj"
cpow = ccall (ComplexDouble -> ComplexDouble) "cpow"
cproj = ccall (ComplexDouble -> ComplexDouble) "cproj"
creal = ccall (ComplexDouble -> Double) "creal"
csin = ccall (ComplexDouble -> ComplexDouble) "csin"
csinh = ccall (ComplexDouble -> ComplexDouble) "csinh"
csqrt = ccall (ComplexDouble -> ComplexDouble) "csqrt"
ctan = ccall (ComplexDouble -> ComplexDouble) "ctan"
ctanh = ccall (ComplexDouble -> ComplexDouble) "ctanh"
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
  when (opts ^. showTokens) $ do
    putStrLn "Tokens:"
    for_ ts $ putStrLn . ppShow
  case p ts of
    Bad e -> failIO $ "Parse Failed: " ++ e
    Ok tree -> return tree

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

transOpts :: Opts -> [String]
transOpts opts = execWriter $ do
  when (opts ^. doRefresh) $ tell ["Fresh"]
  when (opts ^. doSeq)     $ tell ["Sequential"]
  when (opts ^. doFuse)    $ tell ["Fused"]
  when (opts ^. doReduce)  $ tell ["Reduced"]
  when (opts ^. doExpand)  $ tell ["Expanded"]

transP :: Opts -> Program -> IO ()
transP opts prg = do
  tcenv <- runErr . runTCOpts defaultTCOpts . errorScope "prims" . checkProgram $ addPrims (not (opts ^. noPrims)) ø
  transP' opts (tcenv & tcOpts .~ opts ^. checkOpts) prg

transP' :: Opts -> TCEnv -> Program -> IO ()
transP' opts tcenv prg = do
  when (tops /= [] && opts ^. noNorm) $
    usage "--no-norm cannot be combined with --fresh, --expand, --reduce, --seq, or --fuse"
  when (opts ^. showAST) $
    case tops of
      [] | opts ^. noNorm -> putStrLn $ "\n{- Abstract Syntax -}\n\n" ++ ppShow prg
         | otherwise      -> putStrLn $ "\n{- Abstract Syntax of Normalized program -}\n\n" ++ ppShow nprg
      _                   -> putStrLn $ "\n{- Abstract Syntax of " ++ unwords tops ++ " program -}\n\n" ++ ppShow eprg
  when (opts ^. check) $ do
    void . runErr . runTCEnv tcenv $ checkProgram nprg
    putStrLn "Checking successful!"
  when (opts ^. showPretty) $
    case tops of
      [] | opts ^. noNorm -> putStrLn $ "\n{- Pretty-printed program -}\n\n" ++ pretty prg
         | otherwise      -> putStrLn $ "\n{- Normalized program -}\n\n" ++ pretty nprg
      _                   -> putStrLn $ "\n{- " ++ unwords tops ++ " program -}\n\n" ++ pretty eprg
  when (opts ^. compile) $
    putStrLn $ "\n/* C program */\n\n" ++ C.printTree cprg
  unless (opts ^. showPretty || opts ^. showAST || opts ^. compile) $
    -- if we don't print any term we should at least force the result
    length (show eprg) `seq` return ()

  where
    pdefs = tcenv ^. edefs
    tops = transOpts opts
    nprg = norm prg
    rprg | opts ^. doRefresh = transProgramDecs (const hDec) nprg
         | otherwise         = nprg
    sprg | opts ^. doSeq     = Sequential.transProgram (opts ^. seqGas) pdefs rprg
         | otherwise         = rprg
    fprg | opts ^. doFuse    = fuseProgram pdefs sprg
         | otherwise         = sprg
    wprg | opts ^. doReduce  = transProgramTerms (\defs -> reduceL . Scoped (pdefs <> defs) ø) fprg
         | otherwise         = fprg
    eprg | opts ^. doExpand  = transProgramTerms (substDefs . (pdefs <>)) wprg
         | otherwise         = wprg
    cprg = Compile.transProgram $ addPrims (opts ^. compilePrims) eprg

flagSpec :: [(String, (Endom Opts, String))]
flagSpec =
  (\(x,y,z) -> (x,(y,z))) <$>
  [ ("check"        , add check                   , "Type check the program (default on)")
  , ("pretty"       , add showPretty              , "Display the program (can be combined with transformations)")
  , ("compile"      , add compile                 , "Display the compiled program (C language)")
  , ("expand"       , add doExpand                , "Rewrite the program with the definitions expanded")
  , ("reduce"       , add doReduce                , "Reduce the program (weak form)")
  , ("fuse"         , add doFuse                  , "Display the fused program")
  , ("seq"          , add doSeq                   , "Display the sequential program")
  , ("refresh"      , add doRefresh               , "Enable the internal renaming using fresh names")
  , ("show-ast"     , add showAST                 , "Display the program as an Abstract Syntax Tree")
  , ("show-tokens"  , add showTokens              , "Display the program as a list of tokens from the lexer")
  , ("debug-check"  , add debugCheck              , "Display debugging information while checking")
  , ("compile-prims", add compilePrims            , "Also compile the primitive definitions")
  , ("strict-par"   , add (checkOpts . strictPar) , "Make the checker stricter about pars (no mix rule)")
  , ("no-prims"     , add noPrims                 , "Do not include the primitive definitions")
  , ("no-norm"      , add noNorm                  , "Disable the normalizer")
  , ("no-check"     , add noCheck                 , "Disable type checking")
  , ("seq-gas"      , error "seq-gas"             , "Set the maximum number of steps for --seq")
  ] where add opt opts = opts & opt .~ True

usage :: String -> IO a
usage msg = failIO $ unlines (msg : "" : "Usage: ling [option...] [file...]" : "" : "option ::=" : (fmtFlag <$> flagSpec))
  where
    fmtFlag (flag, (_, desc)) = "  | --" ++ pad flag ++ " # " ++ desc
    Just maxlen = maximumOf (each . _1 . to length) flagSpec
    pad s = take maxlen (s ++ repeat ' ')

mainArgs :: Opts -> [String] -> IO ()
mainArgs opts = \case
  [] -> getContents >>= run opts pProgram >>= transP opts
  ("--help":_) -> usage ""
  ("--seq-gas":args) ->
    case args of
      [] -> usage "Missing argument for --seq-gas"
      s:args'
         | all isDigit s -> mainArgs (opts & seqGas .~ read s) args'
         | otherwise     -> usage "Unexpected value for --seq-gas"
  ('-':'-':arg@(_:_)):args ->
    case lookup arg flagSpec of
      Just (opt, _) -> mainArgs (opt opts) args
      _             -> usage $ "Unexpected flag --" ++ arg
  [f] -> runProgram opts f
  fs  -> for_ fs $ \f -> putStrLn f >> runProgram opts f

main :: IO ()
main = mainArgs defaultOpts =<< getArgs
