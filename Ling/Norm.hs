{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Ling.Norm
  ( module Ling.Norm
  , Name(..)
  , Literal(..)
  ) where

import           Ling.Abs     (Literal (..), Name (Name))
import           Ling.Utils

import           Control.Lens

type ChanDec = Arg (Maybe RSession)
type VarDec  = Arg Typ

data Program = Program { _prgDecs :: [Dec] }
  deriving (Eq,Ord,Show,Read)

data Dec
  = Sig Name (Maybe Typ) (Maybe Term)
  | Dat Name [Name]
  | Assert Assertion
  deriving (Eq,Ord,Show,Read)

data Assertion
  = Equal Term Term Typ
  deriving (Eq,Ord,Show,Read)

infixr 4 `Dot`

-- See `Ling.WellFormed` for the conditions on Proc
data Proc = Dot { _procPref :: Pref, _procProcs :: Procs }
  deriving (Eq,Ord,Show,Read)

type Pref  = [Act]
type Procs = [Proc]

data TraverseKind
  = ParK
  | TenK
  | SeqK
  deriving (Eq,Ord,Show,Read)

data Act
  = Nu       ChanDec ChanDec
  | Split    TraverseKind Channel [ChanDec]
  | Send     Channel Term
  | Recv     Channel VarDec
  | NewSlice [Channel] Term Name
  | Ax       Session [Channel]
  | At       Term [Channel]
  deriving (Eq,Ord,Show,Read)

type Branch = (Name,Term)

type Typ = Term
data Term
  = Def Name [Term]
  | Lit Literal
  | Lam VarDec Term
  | Con Name
  | Case Term [Branch]
  --          ^ Sorted
  | Proc [ChanDec] Proc
  | TTyp
  | TFun VarDec Typ
  | TSig VarDec Typ
  | TProto [RSession]
  | TSession Session
  deriving (Eq,Ord,Show,Read)

tSession :: Session -> Term
tSession (TermS NoOp t) = t
tSession             s  = TSession s

-- Polarity with a read/write (recv/send) flavor
data RW = Read | Write
  deriving (Eq,Ord,Show,Read)

data DualOp = DualOp | NoOp | LogOp | SinkOp
  deriving (Eq,Ord,Show,Read)

data Session
  = TermS DualOp Term
  | IO RW VarDec Session
  | Array TraverseKind Sessions
  deriving (Eq,Ord,Show,Read)

depSend, depRecv :: VarDec -> Session -> Session
depSend = IO Write
depRecv = IO Read

sendS, recvS :: Typ -> Session -> Session
sendS = depSend . anonArg
recvS = depRecv . anonArg

data RSession
  = Repl { _rsession :: Session
         , _rfactor  :: Term
         }
  deriving (Eq,Ord,Show,Read)

type Sessions = [RSession]
type NSession = Maybe Session

makeLenses ''Proc
makeLenses ''Program
makeLenses ''RSession

instance Monoid Program where
  mempty        = Program []
  mappend p0 p1 = Program $ p0^.prgDecs ++ p1^.prgDecs

instance Monoid Proc where
  mempty         = [] `Dot` []
  mappend        = parP
    where
      ([] `Dot` ps) `parP` ([] `Dot` qs) = mconcat $ ps ++ qs
      ([] `Dot` ps) `parP` p             = mconcat $ ps ++ [p]
      p             `parP` ([] `Dot` ps) = mconcat $ p : ps
      (ps `Dot` []) `parP` (qs `Dot` []) = (ps ++ qs) `Dot` []
      p0            `parP` p1            = mconcat   [p0,p1]
  mconcat []     = mempty
  mconcat [proc] = proc
  mconcat procs  = [] `Dot` procs

vecTyp :: Typ -> Term -> Typ
vecTyp t e = Def (Name "Vec") [t,e]

intTyp :: Typ
intTyp = Def (Name "Int") []

doubleTyp :: Typ
doubleTyp = Def (Name "Double") []

stringTyp :: Typ
stringTyp = Def (Name "String") []

charTyp :: Typ
charTyp = Def (Name "Char") []

sessionTyp :: Typ
sessionTyp = Def (Name "Session") []

multName :: Name
multName = Name "_*_"

actVarDecs :: Act -> [VarDec]
actVarDecs = \case
  Recv _ a       -> [a]
  NewSlice _ _ x -> [Arg x intTyp]
  _              -> []

kindLabel :: TraverseKind -> String
kindLabel ParK = "par/⅋"
kindLabel TenK = "tensor/⊗"
kindLabel SeqK = "sequence/»"

actLabel :: Act -> String
actLabel = \case
  Nu{}        -> "new"
  Split k _ _ -> "split:" ++ kindLabel k
  Send{}      -> "send"
  Recv{}      -> "recv"
  NewSlice{}  -> "slice"
  Ax{}        -> "fwd"
  At{}        -> "@"

actNeedsDot :: Act -> Bool
actNeedsDot = \case
  Nu{}       -> False
  Split{}    -> False
  Send{}     -> True
  Recv{}     -> True
  NewSlice{} -> True
  Ax{}       -> True
  At{}       -> True

isSendRecv :: Act -> Bool
isSendRecv = \case
  Recv{}     -> True
  Send{}     -> True
  Split{}    -> False
  NewSlice{} -> False
  Nu{}       -> False
  Ax{}       -> False
  At{}       -> False

allSndRcv :: Session -> Bool
allSndRcv = \case
  IO _ _ s   -> allSndRcv s
  Array _ [] -> True
  _          -> False

mkCase :: Term -> [Branch] -> Term
mkCase e brs = case e of
  Con c
    | Just rhs <- lookup c brs -> rhs
    | otherwise -> error $ "mkCase: IMPOSSIBLE no branch for constructor " ++ show c
  _ -> Case e brs
