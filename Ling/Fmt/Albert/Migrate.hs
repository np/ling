{-# LANGUAGE LambdaCase #-}
module Ling.Fmt.Albert.Migrate where

import qualified Ling.Raw            as L
import           Ling.Fmt.Albert.Abs

transName :: Name -> L.Name
transName x = case x of
  Name string -> L.Name string

transProgram :: Program -> L.Program
transProgram x = case x of
  Prg decs -> L.Prg (transDec <$> decs)

transDec :: Dec -> L.Dec
transDec x = case x of
  DPrc name chandecs proc _ ->
    L.DDef (transName name) L.NoSig (L.TProc (transChanDec <$> chandecs) (transProc proc))
  DDef name optsig (SoProc proc) _ ->
    L.DDef (transName name) (transOptSig optsig) (L.TProc [] (transProc proc))
  DDef name optsig (SoTerm term) _ ->
    L.DDef (transName name) (transOptSig optsig) (transTerm term)
  DSig name term _ -> L.DSig (transName name) (transTerm term)
  DDat name connames _ -> L.DDat (transName name) (transConName <$> connames)
  DAsr assertion -> L.DAsr (transAssertion assertion)

transAssertion :: Assertion -> L.Assertion
transAssertion x = case x of
  AEq term1 term2 term3 -> L.AEq (transTerm term1) (transTerm term2) (transTerm term3)

transConName :: ConName -> L.ConName
transConName x = case x of
  CN name -> L.CN (transName name)

transOptSig :: OptSig -> L.OptSig
transOptSig x = case x of
  NoSig -> L.NoSig
  SoSig term -> L.SoSig (transTerm term)

transVarDec :: VarDec -> L.VarDec
transVarDec x = case x of
  VD name term -> L.VD (transName name) (transTerm term)

transVarsDec :: VarsDec -> L.VarsDec
transVarsDec x = case x of
  VsD name names term -> L.VsD (transName name) (transName <$> names) (transTerm term)

transChanDec :: ChanDec -> L.ChanDec
transChanDec x = case x of
  CD name optsession -> L.CD (transName name) (transOptSession optsession)

transBranch :: Branch -> L.Branch
transBranch x = case x of
  Br conname term -> L.Br (transConName conname) (transTerm term)

transLiteral :: Literal -> L.Literal
transLiteral x = case x of
  LInteger i -> L.LInteger i
  LDouble  d -> L.LDouble  d
  LChar    c -> L.LChar    c
  LString  s -> L.LString  s

transATerm :: ATerm -> L.ATerm
transATerm x = case x of
  Var name -> L.Var (transName name)
  Lit literal -> L.Lit (transLiteral literal)
  Con conname -> L.Con (transConName conname)
  TTyp -> L.TTyp
  TProto rsessions -> L.TProto (transRSession <$> rsessions)
  Paren term optsig -> L.Paren (transTerm term) (transOptSig optsig)
  End -> L.End
  Par rsessions -> L.Par (transRSession <$> rsessions)
  Ten rsessions -> L.Ten (transRSession <$> rsessions)
  Seq rsessions -> L.Seq (transRSession <$> rsessions)

transDTerm :: DTerm -> L.DTerm
transDTerm x = case x of
  DTTyp name aterms -> L.DTTyp (transName name) (transATerm <$> aterms)
  DTBnd name term -> L.DTBnd (transName name) (transTerm term)

transTerm :: Term -> L.Term
transTerm x = case x of
  RawApp aterm aterms -> L.RawApp (transATerm aterm) (transATerm <$> aterms)
  Case term branchs -> L.Case (transTerm term) (transBranch <$> branchs)
  TFun term1 term2 -> L.TFun (transTerm term1) (transTerm term2)
  TSig term1 term2 -> L.TSig (transTerm term1) (transTerm term2)
  Lam  varsdec varsdecs term -> L.Lam  (transVarsDec varsdec) (transVarsDec <$> varsdecs) (transTerm term)
  TProc chandecs proc -> L.TProc (transChanDec <$> chandecs) (transProc proc)
  Snd dterm csession -> L.Snd (transDTerm dterm) (transCSession csession)
  Rcv dterm csession -> L.Rcv (transDTerm dterm) (transCSession csession)
  Dual session -> L.Dual (transTerm session)
  Loli session1 session2 -> L.Loli (transTerm session1) (transTerm session2)

transProc :: Proc -> L.Proc
transProc = \case
  PAct act        -> L.PAct (transAct act)
  PNxt proc proc' -> transProc proc `L.PNxt` transProc proc'
  PDot proc proc' -> transProc proc `L.PDot` transProc proc'
  PPrll procs     -> L.PPrll $ transProc <$> procs

transAct :: Act -> L.Act
transAct = \case
  Nu chandec1 chandec2 -> L.Nu (transChanDec chandec1) (transChanDec chandec2)
  ParSplit name chandecs -> L.ParSplit (transName name) (transChanDec <$> chandecs)
  TenSplit name chandecs -> L.TenSplit (transName name) (transChanDec <$> chandecs)
  SeqSplit name chandecs -> L.SeqSplit (transName name) (transChanDec <$> chandecs)
  Send name aterm -> L.Send (transName name) (transATerm aterm)
  Recv name vardec -> L.Recv (transName name) (transVarDec vardec)
  NewSlice chandecs aterm name -> L.NewSlice (transChanDec <$> chandecs) (transATerm aterm) (transName name)
  Ax session chandecs -> L.Ax (transASession session) (transChanDec <$> chandecs)
  SplitAx integer session name -> L.SplitAx integer (transASession session) (transName name)
  At aterm topcpatt -> L.At (transATerm aterm) (transTopCPatt topcpatt)

transOptSession :: OptSession -> L.OptSession
transOptSession x = case x of
  NoSession -> L.NoSession
  SoSession rsession -> L.SoSession (transRSession rsession)

transASession :: ASession -> L.ASession
transASession (AS aterm)= L.AS (transATerm aterm)

transRSession :: RSession -> L.RSession
transRSession x = case x of
  Repl session optrepl -> L.Repl (transTerm session) (transOptRepl optrepl)

transOptRepl :: OptRepl -> L.OptRepl
transOptRepl x = case x of
  One -> L.One
  Some aterm -> L.Some (transATerm aterm)

transCSession :: CSession -> L.CSession
transCSession x = case x of
  Cont session -> L.Cont (transTerm session)
  Done -> L.Done

transTopCPatt :: TopCPatt -> L.TopCPatt
transTopCPatt = \case
  OldTopPatt chandecs -> L.OldTopPatt (transChanDec <$> chandecs)
  ParTopPatt cpatts -> L.ParTopPatt (transCPatt <$> cpatts)
  TenTopPatt cpatts -> L.TenTopPatt (transCPatt <$> cpatts)
  SeqTopPatt cpatts -> L.SeqTopPatt (transCPatt <$> cpatts)

transCPatt :: CPatt -> L.CPatt
transCPatt = \case
  ChaPatt chandec -> L.ChaPatt (transChanDec chandec)
  ParPatt cpatts -> L.ParPatt (transCPatt <$> cpatts)
  TenPatt cpatts -> L.TenPatt (transCPatt <$> cpatts)
  SeqPatt cpatts -> L.SeqPatt (transCPatt <$> cpatts)
