module Ling.Skel where

-- Haskell module generated by the BNF converter

import Ling.Abs
import Ling.ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transName :: Name -> Result
transName x = case x of
  Name string -> failure x
transProgram :: Program -> Result
transProgram x = case x of
  Prg decs -> failure x
transDec :: Dec -> Result
transDec x = case x of
  DDef name optsig term -> failure x
  DSig name term -> failure x
  DDat name connames -> failure x
  DAsr assertion -> failure x
transAssertion :: Assertion -> Result
transAssertion x = case x of
  AEq term1 term2 optsig -> failure x
transConName :: ConName -> Result
transConName x = case x of
  CN name -> failure x
transOptSig :: OptSig -> Result
transOptSig x = case x of
  NoSig -> failure x
  SoSig term -> failure x
transVarDec :: VarDec -> Result
transVarDec x = case x of
  VD name optsig -> failure x
transChanDec :: ChanDec -> Result
transChanDec x = case x of
  CD name optsession -> failure x
transBranch :: Branch -> Result
transBranch x = case x of
  Br conname term -> failure x
transLiteral :: Literal -> Result
transLiteral x = case x of
  LInteger integer -> failure x
  LDouble double -> failure x
  LString string -> failure x
  LChar char -> failure x
transATerm :: ATerm -> Result
transATerm x = case x of
  Var name -> failure x
  Lit literal -> failure x
  Con conname -> failure x
  TTyp -> failure x
  TProto rsessions -> failure x
  Paren term optsig -> failure x
  End -> failure x
  Par rsessions -> failure x
  Ten rsessions -> failure x
  Seq rsessions -> failure x
transTerm :: Term -> Result
transTerm x = case x of
  RawApp aterm aterms -> failure x
  Case term branchs -> failure x
  Snd term csession -> failure x
  Rcv term csession -> failure x
  Dual term -> failure x
  Loli term1 term2 -> failure x
  TFun term1 term2 -> failure x
  TSig term1 term2 -> failure x
  Let name optsig term1 term2 -> failure x
  Lam term1 term2 -> failure x
  TProc chandecs proc -> failure x
transProc :: Proc -> Result
transProc x = case x of
  PAct act -> failure x
  PPrll procs -> failure x
  PNxt proc1 proc2 -> failure x
  PDot proc1 proc2 -> failure x
transAct :: Act -> Result
transAct x = case x of
  Nu chandecs -> failure x
  ParSplit name chandecs -> failure x
  TenSplit name chandecs -> failure x
  SeqSplit name chandecs -> failure x
  Send name aterm -> failure x
  Recv name vardec -> failure x
  NewSlice chandecs aterm name -> failure x
  Ax asession chandecs -> failure x
  SplitAx integer asession name -> failure x
  At aterm topcpatt -> failure x
  LetA name optsig aterm -> failure x
transASession :: ASession -> Result
transASession x = case x of
  AS aterm -> failure x
transTopCPatt :: TopCPatt -> Result
transTopCPatt x = case x of
  OldTopPatt chandecs -> failure x
  ParTopPatt cpatts -> failure x
  TenTopPatt cpatts -> failure x
  SeqTopPatt cpatts -> failure x
transCPatt :: CPatt -> Result
transCPatt x = case x of
  ChaPatt chandec -> failure x
  ParPatt cpatts -> failure x
  TenPatt cpatts -> failure x
  SeqPatt cpatts -> failure x
transOptSession :: OptSession -> Result
transOptSession x = case x of
  NoSession -> failure x
  SoSession rsession -> failure x
transRSession :: RSession -> Result
transRSession x = case x of
  Repl term optrepl -> failure x
transOptRepl :: OptRepl -> Result
transOptRepl x = case x of
  One -> failure x
  Some aterm -> failure x
transCSession :: CSession -> Result
transCSession x = case x of
  Cont term -> failure x
  Done -> failure x

