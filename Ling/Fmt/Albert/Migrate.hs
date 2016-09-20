{-# LANGUAGE LambdaCase #-}

module Ling.Fmt.Albert.Migrate where

import           Ling.Fmt.Albert.Abs
import qualified Ling.Fmt.Benjamin.Abs as L

transName :: Name -> L.Name
transName = \case
  Name string -> L.Name string

transProgram :: Program -> L.Program
transProgram = \case
  Prg decs -> L.Prg (transDec <$> decs)

transDec :: Dec -> L.Dec
transDec = \case
  DPrc name chandecs proc0 _ ->
    L.DDef (transName name) L.NoSig (L.TProc (transChanDec <$> chandecs) (transProc proc0))
  DDef name optsig (SoProc proc0) _ ->
    L.DDef (transName name) (transOptSig optsig) (L.TProc [] (transProc proc0))
  DDef name optsig (SoTerm term) _ ->
    L.DDef (transName name) (transOptSig optsig) (transTerm term)
  DSig name term _ -> L.DSig (transName name) (transTerm term)
  DDat name connames _ -> L.DDat (transName name) (transConName <$> connames)
  DAsr assertion -> L.DAsr (transAssertion assertion)

transAssertion :: Assertion -> L.Assertion
transAssertion = \case
  AEq term1 term2 optsig -> L.AEq (transTerm term1) (transTerm term2) (transOptSig optsig)

transConName :: ConName -> L.ConName
transConName = \case
  CN name -> L.CN (transName name)

transOptSig :: OptSig -> L.OptSig
transOptSig = \case
  NoSig      -> L.NoSig
  SoSig term -> L.SoSig (transTerm term)

transVarDec :: VarDec -> L.VarDec
transVarDec = \case
  VD name optsig -> L.VD (transName name) (transOptSig optsig)

transChanDec :: ChanDec -> L.ChanDec
transChanDec = \case
  CD name optrepl optsession -> L.CD (transName name) (transOptRepl optrepl) (transOptSession optsession)

transBranch :: Branch -> L.Branch
transBranch = \case
  Br conname term -> L.Br (transConName conname) (transTerm term)

transLiteral :: Literal -> L.Literal
transLiteral = \case
  LInteger i -> L.LInteger i
  LDouble d  -> L.LDouble d
  LChar c    -> L.LChar c
  LString s  -> L.LString s

transATerm :: ATerm -> L.ATerm
transATerm = \case
  Var name          -> L.Var (transName name)
  Op opname         -> L.Op (transOpName opname)
  Lit literal       -> L.Lit (transLiteral literal)
  Con conname       -> L.Con (transConName conname)
  TTyp              -> L.TTyp
  TProto rsessions  -> L.TProto (transRSession <$> rsessions)
  Paren term optsig -> L.Paren (transTerm term) (transOptSig optsig)
  End               -> L.End
  Par rsessions     -> L.Par (transRSession <$> rsessions)
  Ten rsessions     -> L.Ten (transRSession <$> rsessions)
  Seq rsessions     -> L.Seq (transRSession <$> rsessions)

transTerm :: Term -> L.Term
transTerm = \case
  RawApp aterm aterms    -> L.RawApp (transATerm aterm) (transATerm <$> aterms)
  Case term branchs      -> L.Case (transTerm term) (transBranch <$> branchs)
  Lam term1 term2        -> L.Lam (transTerm term1) (transTerm term2)
  TFun term1 term2       -> L.TFun (transTerm term1) (transTerm term2)
  TSig term1 term2       -> L.TSig (transTerm term1) (transTerm term2)
  TProc chandecs proc0   -> L.TProc (transChanDec <$> chandecs) (transProc proc0)
  Snd term csession      -> L.Snd (transTerm term) (transCSession csession)
  Rcv term csession      -> L.Rcv (transTerm term) (transCSession csession)
  Dual session           -> L.Dual (transTerm session)
  Loli session1 session2 -> L.Loli (transTerm session1) (transTerm session2)
  Let x os t u           -> L.Let (transName x) (transOptSig os)
                                  (transTerm t) (transTerm u)
  TRecv x                -> L.TRecv (transName x)

transProc :: Proc -> L.Proc
transProc = \case
  PAct act         -> L.PAct (transAct act)
  PNxt proc0 proc1 -> transProc proc0 `L.PNxt` transProc proc1
  PDot proc0 proc1 -> transProc proc0 `L.PDot` transProc proc1
  PSem proc0 proc1 -> transProc proc0 `L.PSem` transProc proc1
  PPrll procs      -> L.PPrll $ transProc <$> procs
  NewSlice chandecs aterm name proc0 ->
    L.NewSlice (transChanDec <$> chandecs) (transATerm aterm)
               (transName name) (transProc proc0)

transAct :: Act -> L.Act
transAct = \case
  Nu newalloc -> L.Nu (transNewAlloc newalloc)
  ParSplit chan chandecs -> L.ParSplit (L.NoSplit (transName chan)) (transChanDec <$> chandecs)
  TenSplit chan chandecs -> L.TenSplit (L.NoSplit (transName chan)) (transChanDec <$> chandecs)
  SeqSplit chan chandecs -> L.SeqSplit (L.NoSplit (transName chan)) (transChanDec <$> chandecs)
  Send name aterm -> L.Send (transName name) (transATerm aterm)
  Recv name vardec -> L.Recv (transName name) (transVarDec vardec)
  NewSend name aterm -> L.NewSend (transName name) L.NoSession (transATerm aterm)
  NewRecv name optsig chan -> L.NewRecv (transName name) (transOptSig optsig) (transName chan)
  Ax session chandecs -> L.Ax (transASession session) (transChanDec <$> chandecs)
  SplitAx integer session name -> L.SplitAx integer (transASession session) (transName name)
  At aterm topcpatt -> L.At (transATerm aterm) (transTopCPatt topcpatt)
  LetA x os t -> L.LetA (transName x) (transOptSig os) (transATerm t)
  LetRecv x os t -> L.LetRecv (transName x) (transOptSig os) (transATerm t)

transAllocTerm :: AllocTerm -> L.AllocTerm
transAllocTerm (AVar d) = L.AVar (transName d)
transAllocTerm (ALit lit) = L.ALit (transLiteral lit)
transAllocTerm (AParen t os) = L.AParen (transTerm t) (transOptSig os)

transNewPatt :: NewPatt -> L.NewPatt
transNewPatt (TenNewPatt chandecs) = L.TenNewPatt (L.ChaPatt . transChanDec <$> chandecs)
transNewPatt (SeqNewPatt chandecs) = L.SeqNewPatt (L.ChaPatt . transChanDec <$> chandecs)

transNewAlloc :: NewAlloc -> L.NewAlloc
transNewAlloc (New newpatt) = L.New (transNewPatt newpatt)
transNewAlloc (OldNew chandecs) = L.OldNew (transChanDec <$> chandecs)
transNewAlloc (NewSAnn term optsig newpatt) = L.NewSAnn (transTerm term) (transOptSig optsig) (transNewPatt newpatt)
transNewAlloc (NewNAnn opnname allocterms newpatt) = L.NewNAnn (transOpName opnname) (transAllocTerm <$> allocterms) (transNewPatt newpatt)

transOpName :: OpName -> L.OpName
transOpName (OpName x) = L.OpName x

transOptSession :: OptSession -> L.OptSession
transOptSession = \case
  NoSession          -> L.NoSession
  SoSession rsession -> L.SoSession (transRSession rsession)

transASession :: ASession -> L.ASession
transASession (AS aterm) = L.AS (transATerm aterm)

transRSession :: RSession -> L.RSession
transRSession = \case
  Repl session optrepl -> L.Repl (transTerm session) (transOptRepl optrepl)

transOptRepl :: OptRepl -> L.OptRepl
transOptRepl = \case
  One        -> L.One
  Some aterm -> L.Some (transATerm aterm)

transCSession :: CSession -> L.CSession
transCSession = \case
  Cont session -> L.Cont (transTerm session)
  Done         -> L.Done

transTopCPatt :: TopCPatt -> L.TopCPatt
transTopCPatt = \case
  OldTopPatt chandecs -> L.OldTopPatt (transChanDec <$> chandecs)
  ParTopPatt cpatts   -> L.ParTopPatt (transCPatt <$> cpatts)
  TenTopPatt cpatts   -> L.TenTopPatt (transCPatt <$> cpatts)
  SeqTopPatt cpatts   -> L.SeqTopPatt (transCPatt <$> cpatts)

transCPatt :: CPatt -> L.CPatt
transCPatt = \case
  ChaPatt chandec -> L.ChaPatt (transChanDec chandec)
  ParPatt cpatts  -> L.ParPatt (transCPatt <$> cpatts)
  TenPatt cpatts  -> L.TenPatt (transCPatt <$> cpatts)
  SeqPatt cpatts  -> L.SeqPatt (transCPatt <$> cpatts)
