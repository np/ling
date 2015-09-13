module Ling.Norm where

import Ling.Abs (Name(Name))
import Ling.Utils

type ChanDec = Arg (Maybe RSession)
type VarDec  = Arg Typ

data Program = Program [Dec]
  deriving (Eq,Ord,Show,Read)

data Dec
  = Dec Name [ChanDec] Proc
  | Sig Name Typ (Maybe Term)
  | Dat Name [Name]
  deriving (Eq,Ord,Show,Read)

data Proc
  = Act [Pref] Procs
  | At Term [Channel]
  | Ax Session Channel Channel [Channel]
  deriving (Eq,Ord,Show,Read)

type Procs = [Proc]

data TraverseKind
  = ParK
  | TenK
  | SeqK
  deriving (Eq,Ord,Show,Read)

type Act = Pref
data Pref
  = Nu       ChanDec ChanDec
  | Split    TraverseKind Channel [ChanDec]
  | Send     Channel Term
  | Recv     Channel VarDec
  | NewSlice [Channel] Term Name
  deriving (Eq,Ord,Show,Read)

type Typ = Term
data Term
  = Def Name [Term]
  | Lit Integer
  | Lam VarDec Term
  | Con Name
  | Case Term [(Name,Term)]
  --          ^ Sorted
  | Proc [ChanDec] Proc
  | TTyp
  | TFun VarDec Typ
  | TSig VarDec Typ
  | TProto [RSession]
  deriving (Eq,Ord,Show,Read)

-- Polarity with a read/write (recv/send) flavor
data RW = Read | Write
  deriving (Eq,Ord,Show,Read)

data Session
  = Atm RW Name
  | End
  | Snd Typ Session
  | Rcv Typ Session
  | Par Sessions
  | Ten Sessions
  | Seq Sessions
  deriving (Eq,Ord,Show,Read)

data RSession
  = Repl Session Term
  deriving (Eq,Ord,Show,Read)

type Sessions = [RSession]
type NSession = Maybe Session

vec :: Typ -> Term -> Typ
vec t e = Def (Name "Vec") [t,e]

int :: Typ
int = Def (Name "Int") []

tSession :: Typ
tSession = Def (Name "Session") []

multName :: Name
multName = Name "_*_"

actVarDecs :: Pref -> [VarDec]
actVarDecs pref =
  case pref of
    Recv _ a       -> [a]
    NewSlice _ _ x -> [Arg x int]
    _              -> []

kindLabel :: TraverseKind -> String
kindLabel ParK = "par/⅋"
kindLabel TenK = "tensor/⊗"
kindLabel SeqK = "sequence/»"

actLabel :: Pref -> String
actLabel Nu{}          = "new"
actLabel (Split k _ _) = "split:" ++ kindLabel k
actLabel Send{}        = "send"
actLabel Recv{}        = "recv"
actLabel NewSlice{}    = "slice"
