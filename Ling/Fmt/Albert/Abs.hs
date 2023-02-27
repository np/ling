-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language Albert.

module Ling.Fmt.Albert.Abs where

import Prelude (Char, Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Program = Prg [Dec]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Dec
    = DPrc Name [ChanDec] Proc OptDot
    | DDef Name OptSig TermProc OptDot
    | DSig Name Term OptDot
    | DDat Name [ConName] OptDot
    | DAsr Assertion
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Assertion = AEq Term Term OptSig
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ConName = CN Name
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data OptDot = NoDot | SoDot
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TermProc = SoTerm Term | SoProc Proc
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data OptSig = NoSig | SoSig Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VarDec = VD Name OptSig
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ChanDec = CD Name OptRepl OptSession
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Branch = Br ConName Term
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Literal
    = LInteger Integer | LDouble Double | LString String | LChar Char
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ATerm
    = Var Name
    | Op OpName
    | Lit Literal
    | Con ConName
    | TTyp
    | TProto [RSession]
    | Paren Term OptSig
    | End
    | Par [RSession]
    | Ten [RSession]
    | Seq [RSession]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Term
    = RawApp ATerm [ATerm]
    | Case Term [Branch]
    | Snd Term CSession
    | Rcv Term CSession
    | Dual Term
    | TRecv Name
    | Loli Term Term
    | TFun Term Term
    | TSig Term Term
    | Let Name OptSig Term Term
    | Lam Term Term
    | TProc [ChanDec] Proc
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Proc
    = PAct Act
    | PPrll [Proc]
    | PNxt Proc Proc
    | PDot Proc Proc
    | PSem Proc Proc
    | NewSlice [ChanDec] ATerm Name Proc
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Act
    = Nu NewAlloc
    | ParSplit Name [ChanDec]
    | TenSplit Name [ChanDec]
    | SeqSplit Name [ChanDec]
    | Send Name ATerm
    | NewSend Name ATerm
    | Recv Name VarDec
    | NewRecv Name OptSig Name
    | LetRecv Name OptSig ATerm
    | Ax ASession [ChanDec]
    | SplitAx Integer ASession Name
    | At ATerm TopCPatt
    | LetA Name OptSig ATerm
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ASession = AS ATerm
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TopCPatt
    = OldTopPatt [ChanDec]
    | ParTopPatt [CPatt]
    | TenTopPatt [CPatt]
    | SeqTopPatt [CPatt]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CPatt
    = ChaPatt ChanDec
    | ParPatt [CPatt]
    | TenPatt [CPatt]
    | SeqPatt [CPatt]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data OptSession = NoSession | SoSession RSession
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data RSession = Repl Term OptRepl
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data OptRepl = One | Some ATerm
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CSession = Cont Term | Done
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data AllocTerm = AVar Name | ALit Literal
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data NewPatt = TenNewPatt [ChanDec] | SeqNewPatt [ChanDec]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data NewAlloc
    = OldNew [ChanDec]
    | New NewPatt
    | NewSAnn Term OptSig NewPatt
    | NewNAnn OpName [AllocTerm] NewPatt
  deriving (C.Eq, C.Ord, C.Show, C.Read)

newtype Name = Name String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

newtype OpName = OpName String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)
