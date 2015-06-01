module Lin.Norm where

import Lin.Abs (Name(Name))
import Lin.Utils

type ChanDec = Arg (Maybe Session)
type VarDec  = Arg Typ

data Program = Program [Dec]
  deriving (Eq,Ord,Show,Read)

data Dec
  = Dec Name [ChanDec] Proc
  | Sig Name Term
  deriving (Eq,Ord,Show,Read)

data Proc
  = Act [Pref] Procs
  | Ax Session Channel Channel [Channel]
  | At Term [Channel]
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
  | NewSlice Term Name
  deriving (Eq,Ord,Show,Read)

type Typ = Term
data Term
  = Def Name [Term]
  | Lit Integer
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
