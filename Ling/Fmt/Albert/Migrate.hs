module Ling.Fmt.Albert.Migrate where

import qualified Ling.Abs            as L
import           Ling.Fmt.Albert.Abs

transName :: Name -> L.Name
transName x = case x of
  Name string -> L.Name string

transProgram :: Program -> L.Program
transProgram x = case x of
  Prg decs -> L.Prg (map transDec decs)

transDec :: Dec -> L.Dec
transDec x = case x of
  DPrc name chandecs proc _ ->
    L.DDef (transName name) L.NoSig (L.TProc (transChanDecs chandecs) (transProc proc))
  DDef name optsig (SoProc proc) _ ->
    L.DDef (transName name) (transOptSig optsig) (L.TProc [] (transProc proc))
  DDef name optsig (SoTerm term) _ ->
    L.DDef (transName name) (transOptSig optsig) (transTerm term)
  DSig name term _ -> L.DSig (transName name) (transTerm term)
  DDat name connames _ -> L.DDat (transName name) (map transConName connames)

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

transChanDecs :: [ChanDec] -> [L.ChanDec]
transChanDecs = map transChanDec

transChanDec :: ChanDec -> L.ChanDec
transChanDec x = case x of
  CD name optsession -> L.CD (transName name) (transOptSession optsession)

transBranch :: Branch -> L.Branch
transBranch x = case x of
  Br conname term -> L.Br (transConName conname) (transTerm term)

transATerm :: ATerm -> L.ATerm
transATerm x = case x of
  Var name -> L.Var (transName name)
  Lit integer -> L.Lit integer
  Con conname -> L.Con (transConName conname)
  TTyp -> L.TTyp
  TProto rsessions -> L.TProto (map transRSession rsessions)
  Paren term -> L.Paren (transTerm term)

transDTerm :: DTerm -> L.DTerm
transDTerm x = case x of
  DTTyp name aterms -> L.DTTyp (transName name) (map transATerm aterms)
  DTBnd name term -> L.DTBnd (transName name) (transTerm term)

transTerm :: Term -> L.Term
transTerm x = case x of
  RawApp aterm aterms -> L.RawApp (transATerm aterm) (map transATerm aterms)
  Case term branchs -> L.Case (transTerm term) (map transBranch branchs)
  TFun vardec vardecs term -> L.TFun (transVarDec vardec) (map transVarDec vardecs) (transTerm term)
  TSig vardec vardecs term -> L.TSig (transVarDec vardec) (map transVarDec vardecs) (transTerm term)
  Lam vardec vardecs term -> L.Lam (transVarDec vardec) (map transVarDec vardecs) (transTerm term)
  TProc chandecs proc -> L.TProc (map transChanDec chandecs) (transProc proc)

transProc :: Proc -> L.Proc
transProc x = case x of
  Act prefs procs -> L.Act (map transPref prefs) (transProcs procs)

transProcs :: Procs -> L.Procs
transProcs x = case x of
  ZeroP -> L.ZeroP
  Prll procs -> L.Prll (map transProc procs)

transPref :: Pref -> L.Pref
transPref x = case x of
  Nu chandec1 chandec2 -> L.Nu (transChanDec chandec1) (transChanDec chandec2)
  ParSplit name chandecs -> L.ParSplit (transName name) (map transChanDec chandecs)
  TenSplit name chandecs -> L.TenSplit (transName name) (map transChanDec chandecs)
  SeqSplit name chandecs -> L.SeqSplit (transName name) (map transChanDec chandecs)
  Send name aterm -> L.Send (transName name) (transATerm aterm)
  Recv name vardec -> L.Recv (transName name) (transVarDec vardec)
  NewSlice names aterm name -> L.NewSlice (map transName names) (transATerm aterm) (transName name)
  Ax session names -> L.Ax (transSession session) (map transName names)
  SplitAx integer session name -> L.SplitAx integer (transSession session) (transName name)
  At aterm names -> L.At (transATerm aterm) (map transName names)

transOptSession :: OptSession -> L.OptSession
transOptSession x = case x of
  NoSession -> L.NoSession
  SoSession rsession -> L.SoSession (transRSession rsession)

transSession :: Session -> L.Session
transSession x = case x of
  Atm name -> L.Atm (transName name)
  End -> L.End
  Par rsessions -> L.Par (map transRSession rsessions)
  Ten rsessions -> L.Ten (map transRSession rsessions)
  Seq rsessions -> L.Seq (map transRSession rsessions)
  Sort aterm1 aterm2 -> L.Sort (transATerm aterm1) (transATerm aterm2)
  Log session -> L.Log (transSession session)
  Fwd integer session -> L.Fwd integer (transSession session)
  Snd dterm csession -> L.Snd (transDTerm dterm) (transCSession csession)
  Rcv dterm csession -> L.Rcv (transDTerm dterm) (transCSession csession)
  Dual session -> L.Dual (transSession session)
  Loli session1 session2 -> L.Loli (transSession session1) (transSession session2)

transRSession :: RSession -> L.RSession
transRSession x = case x of
  Repl session optrepl -> L.Repl (transSession session) (transOptRepl optrepl)

transOptRepl :: OptRepl -> L.OptRepl
transOptRepl x = case x of
  One -> L.One
  Some aterm -> L.Some (transATerm aterm)

transCSession :: CSession -> L.CSession
transCSession x = case x of
  Cont session -> L.Cont (transSession session)
  Done -> L.Done
