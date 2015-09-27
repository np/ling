-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Ling.Fmt.Albert.Par where
import Ling.Fmt.Albert.Abs
import Ling.Fmt.Albert.Lex
import Ling.Fmt.Albert.ErrM

}

%name pProgram Program
%name pListName ListName
%name pDec Dec
%name pConName ConName
%name pOptDot OptDot
%name pTermProc TermProc
%name pListConName ListConName
%name pOptSig OptSig
%name pListDec ListDec
%name pVarDec VarDec
%name pListVarDec ListVarDec
%name pChanDec ChanDec
%name pListChanDec ListChanDec
%name pBranch Branch
%name pListBranch ListBranch
%name pATerm ATerm
%name pListATerm ListATerm
%name pDTerm DTerm
%name pTerm Term
%name pProc Proc
%name pListProc ListProc
%name pProcs Procs
%name pPref Pref
%name pListPref ListPref
%name pOptSession OptSession
%name pSession4 Session4
%name pSession3 Session3
%name pSession2 Session2
%name pSession Session
%name pRSession RSession
%name pListRSession ListRSession
%name pOptRepl OptRepl
%name pCSession CSession
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '(' { PT _ (TS _ 2) }
  ')' { PT _ (TS _ 3) }
  '**' { PT _ (TS _ 4) }
  ',' { PT _ (TS _ 5) }
  '->' { PT _ (TS _ 6) }
  '-o' { PT _ (TS _ 7) }
  '.' { PT _ (TS _ 8) }
  ':' { PT _ (TS _ 9) }
  ':]' { PT _ (TS _ 10) }
  '<' { PT _ (TS _ 11) }
  '=' { PT _ (TS _ 12) }
  '>' { PT _ (TS _ 13) }
  '?' { PT _ (TS _ 14) }
  '@' { PT _ (TS _ 15) }
  'Fwd' { PT _ (TS _ 16) }
  'Log' { PT _ (TS _ 17) }
  'Sort' { PT _ (TS _ 18) }
  'Type' { PT _ (TS _ 19) }
  '[' { PT _ (TS _ 20) }
  '[:' { PT _ (TS _ 21) }
  '\\' { PT _ (TS _ 22) }
  ']' { PT _ (TS _ 23) }
  '^' { PT _ (TS _ 24) }
  '`' { PT _ (TS _ 25) }
  'as' { PT _ (TS _ 26) }
  'case' { PT _ (TS _ 27) }
  'data' { PT _ (TS _ 28) }
  'end' { PT _ (TS _ 29) }
  'fwd' { PT _ (TS _ 30) }
  'new' { PT _ (TS _ 31) }
  'of' { PT _ (TS _ 32) }
  'proc' { PT _ (TS _ 33) }
  'recv' { PT _ (TS _ 34) }
  'send' { PT _ (TS _ 35) }
  'slice' { PT _ (TS _ 36) }
  '{' { PT _ (TS _ 37) }
  '|' { PT _ (TS _ 38) }
  '}' { PT _ (TS _ 39) }
  '~' { PT _ (TS _ 40) }

L_integ  { PT _ (TI $$) }
L_Name { PT _ (T_Name $$) }


%%

Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
Name    :: { Name} : L_Name { Name ($1)}

Program :: { Program }
Program : ListDec { Ling.Fmt.Albert.Abs.Prg $1 }
ListName :: { [Name] }
ListName : {- empty -} { [] }
         | Name { (:[]) $1 }
         | Name ',' ListName { (:) $1 $3 }
Dec :: { Dec }
Dec : Name '(' ListChanDec ')' '=' Proc OptDot { Ling.Fmt.Albert.Abs.DPrc $1 $3 $6 $7 }
    | Name OptSig '=' TermProc OptDot { Ling.Fmt.Albert.Abs.DDef $1 $2 $4 $5 }
    | Name ':' Term OptDot { Ling.Fmt.Albert.Abs.DSig $1 $3 $4 }
    | 'data' Name '=' ListConName OptDot { Ling.Fmt.Albert.Abs.DDat $2 $4 $5 }
ConName :: { ConName }
ConName : '`' Name { Ling.Fmt.Albert.Abs.CN $2 }
OptDot :: { OptDot }
OptDot : {- empty -} { Ling.Fmt.Albert.Abs.NoDot }
       | '.' { Ling.Fmt.Albert.Abs.SoDot }
TermProc :: { TermProc }
TermProc : Term { Ling.Fmt.Albert.Abs.SoTerm $1 }
         | Proc { Ling.Fmt.Albert.Abs.SoProc $1 }
ListConName :: { [ConName] }
ListConName : {- empty -} { [] }
            | ConName { (:[]) $1 }
            | ConName '|' ListConName { (:) $1 $3 }
OptSig :: { OptSig }
OptSig : {- empty -} { Ling.Fmt.Albert.Abs.NoSig }
       | ':' Term { Ling.Fmt.Albert.Abs.SoSig $2 }
ListDec :: { [Dec] }
ListDec : {- empty -} { [] }
        | Dec { (:[]) $1 }
        | Dec ',' ListDec { (:) $1 $3 }
VarDec :: { VarDec }
VarDec : '(' Name ':' Term ')' { Ling.Fmt.Albert.Abs.VD $2 $4 }
ListVarDec :: { [VarDec] }
ListVarDec : {- empty -} { [] }
           | ListVarDec VarDec { flip (:) $1 $2 }
ChanDec :: { ChanDec }
ChanDec : Name OptSession { Ling.Fmt.Albert.Abs.CD $1 $2 }
ListChanDec :: { [ChanDec] }
ListChanDec : {- empty -} { [] }
            | ChanDec { (:[]) $1 }
            | ChanDec ',' ListChanDec { (:) $1 $3 }
Branch :: { Branch }
Branch : ConName '->' Term { Ling.Fmt.Albert.Abs.Br $1 $3 }
ListBranch :: { [Branch] }
ListBranch : {- empty -} { [] }
           | Branch { (:[]) $1 }
           | Branch ',' ListBranch { (:) $1 $3 }
ATerm :: { ATerm }
ATerm : Name { Ling.Fmt.Albert.Abs.Var $1 }
      | Integer { Ling.Fmt.Albert.Abs.Lit $1 }
      | ConName { Ling.Fmt.Albert.Abs.Con $1 }
      | 'Type' { Ling.Fmt.Albert.Abs.TTyp }
      | '<' ListRSession '>' { Ling.Fmt.Albert.Abs.TProto $2 }
      | '(' Term ')' { Ling.Fmt.Albert.Abs.Paren $2 }
ListATerm :: { [ATerm] }
ListATerm : {- empty -} { [] } | ListATerm ATerm { flip (:) $1 $2 }
DTerm :: { DTerm }
DTerm : Name ListATerm { Ling.Fmt.Albert.Abs.DTTyp $1 (reverse $2) }
      | '(' Name ':' Term ')' { Ling.Fmt.Albert.Abs.DTBnd $2 $4 }
Term :: { Term }
Term : ATerm ListATerm { Ling.Fmt.Albert.Abs.RawApp $1 (reverse $2) }
     | 'case' Term 'of' '{' ListBranch '}' { Ling.Fmt.Albert.Abs.Case $2 $5 }
     | VarDec ListVarDec '->' Term { Ling.Fmt.Albert.Abs.TFun $1 (reverse $2) $4 }
     | VarDec ListVarDec '**' Term { Ling.Fmt.Albert.Abs.TSig $1 (reverse $2) $4 }
     | '\\' VarDec ListVarDec '->' Term { Ling.Fmt.Albert.Abs.Lam $2 (reverse $3) $5 }
     | 'proc' '(' ListChanDec ')' Proc { Ling.Fmt.Albert.Abs.TProc $3 $5 }
Proc :: { Proc }
Proc : ListPref Procs { Ling.Fmt.Albert.Abs.Act (reverse $1) $2 }
ListProc :: { [Proc] }
ListProc : {- empty -} { [] }
         | Proc { (:[]) $1 }
         | Proc '|' ListProc { (:) $1 $3 }
Procs :: { Procs }
Procs : {- empty -} { Ling.Fmt.Albert.Abs.ZeroP }
      | '(' ListProc ')' { Ling.Fmt.Albert.Abs.Prll $2 }
Pref :: { Pref }
Pref : 'new' '(' ChanDec ',' ChanDec ')' { Ling.Fmt.Albert.Abs.Nu $3 $5 }
     | Name '{' ListChanDec '}' { Ling.Fmt.Albert.Abs.ParSplit $1 $3 }
     | Name '[' ListChanDec ']' { Ling.Fmt.Albert.Abs.TenSplit $1 $3 }
     | Name '[:' ListChanDec ':]' { Ling.Fmt.Albert.Abs.SeqSplit $1 $3 }
     | 'send' Name ATerm { Ling.Fmt.Albert.Abs.Send $2 $3 }
     | 'recv' Name VarDec { Ling.Fmt.Albert.Abs.Recv $2 $3 }
     | 'slice' '(' ListName ')' ATerm 'as' Name { Ling.Fmt.Albert.Abs.NewSlice $3 $5 $7 }
     | 'fwd' Session '(' ListName ')' { Ling.Fmt.Albert.Abs.Ax $2 $4 }
     | 'fwd' Integer Session Name { Ling.Fmt.Albert.Abs.SplitAx $2 $3 $4 }
     | '@' ATerm '(' ListName ')' { Ling.Fmt.Albert.Abs.At $2 $4 }
ListPref :: { [Pref] }
ListPref : {- empty -} { [] } | ListPref Pref { flip (:) $1 $2 }
OptSession :: { OptSession }
OptSession : {- empty -} { Ling.Fmt.Albert.Abs.NoSession }
           | ':' RSession { Ling.Fmt.Albert.Abs.SoSession $2 }
Session4 :: { Session }
Session4 : Name { Ling.Fmt.Albert.Abs.Atm $1 }
         | 'end' { Ling.Fmt.Albert.Abs.End }
         | '{' ListRSession '}' { Ling.Fmt.Albert.Abs.Par $2 }
         | '[' ListRSession ']' { Ling.Fmt.Albert.Abs.Ten $2 }
         | '[:' ListRSession ':]' { Ling.Fmt.Albert.Abs.Seq $2 }
         | '(' Session ')' { $2 }
Session3 :: { Session }
Session3 : 'Sort' ATerm ATerm { Ling.Fmt.Albert.Abs.Sort $2 $3 }
         | 'Log' Session4 { Ling.Fmt.Albert.Abs.Log $2 }
         | 'Fwd' Integer Session4 { Ling.Fmt.Albert.Abs.Fwd $2 $3 }
         | Session4 { $1 }
Session2 :: { Session }
Session2 : '!' DTerm CSession { Ling.Fmt.Albert.Abs.Snd $2 $3 }
         | '?' DTerm CSession { Ling.Fmt.Albert.Abs.Rcv $2 $3 }
         | '~' Session2 { Ling.Fmt.Albert.Abs.Dual $2 }
         | Session3 { $1 }
Session :: { Session }
Session : Session2 '-o' Session { Ling.Fmt.Albert.Abs.Loli $1 $3 }
        | Session2 { $1 }
RSession :: { RSession }
RSession : Session OptRepl { Ling.Fmt.Albert.Abs.Repl $1 $2 }
ListRSession :: { [RSession] }
ListRSession : {- empty -} { [] }
             | RSession { (:[]) $1 }
             | RSession ',' ListRSession { (:) $1 $3 }
OptRepl :: { OptRepl }
OptRepl : {- empty -} { Ling.Fmt.Albert.Abs.One }
        | '^' ATerm { Ling.Fmt.Albert.Abs.Some $2 }
CSession :: { CSession }
CSession : '.' Session2 { Ling.Fmt.Albert.Abs.Cont $2 }
         | {- empty -} { Ling.Fmt.Albert.Abs.Done }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
}

