{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
module Ling.Norm
  ( module Ling.Norm
  , Name(..)
  , Literal(..)
  ) where

import           Ling.Abs     (Literal (..), Name (Name))
import           Ling.Prelude

newtype RFactor = RFactor { _rterm :: Term }
  deriving (Eq, Ord, Read, Show)

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

data CPatt
    = ChanP ChanDec
    | ArrayP TraverseKind [CPatt]
  deriving (Eq, Ord, Show, Read)

data Act
  = Nu       ChanDec ChanDec
  -- TODO? Split Channel CPatt
  | Split    TraverseKind Channel [ChanDec]
  | Send     Channel Term
  | Recv     Channel VarDec
  | NewSlice [Channel] RFactor Name
  | Ax       Session [Channel]
  | At       Term CPatt
  deriving (Eq,Ord,Show,Read)

type ConName = Name
type Branch = (ConName,Term)

type Typ = Term
data Term
  = Def Name [Term]
  | Lit Literal
  | Lam VarDec Term
  | Con ConName
  | Case Term [Branch]
  --          ^ Sorted
  | Proc [ChanDec] Proc
  | TTyp
  | TFun VarDec Typ
  | TSig VarDec Typ
  | TProto [RSession]
  | TSession Session
  deriving (Eq,Ord,Show,Read)

tSession :: Iso' Session Term
tSession = iso fwd bkd
  where
    fwd (TermS NoOp t) = t
    fwd             s  = TSession s
    bkd (TSession s)   = s
    bkd           t    = TermS NoOp t

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
         , _rfactor  :: RFactor
         }
  deriving (Eq,Ord,Show,Read)

type Sessions = [RSession]
type NSession = Maybe Session

makeLenses ''RFactor
makeLenses ''Proc
makeLenses ''Program
makeLenses ''RSession
makePrisms ''Dec
makePrisms ''Assertion
makePrisms ''TraverseKind
makePrisms ''CPatt
makePrisms ''Act
makePrisms ''Term
makePrisms ''RW
makePrisms ''DualOp
makePrisms ''Session

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

-- Arbitrary type annotations can be seen as the use of the
-- following definition (the identity function)
-- _:_ :  (A : Type)(x : A)-> A
--     = \(A : Type)(x : A)-> x
--
-- The only twist is that the arguments are reversed:
-- `(t : A)` is represented internally as `_:_ A t`
optSig :: Term -> Maybe Typ -> Term
optSig t = \case
  Nothing -> t
  Just a  -> Def (Name "_:_") [a,t]

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

addName :: Name
addName = Name "_+_"

multName :: Name
multName = Name "_*_"

actVarDecs :: Act -> [VarDec]
actVarDecs = \case
  Recv _ a       -> [a]
  NewSlice _ _ x -> [Arg x intTyp]
  _              -> []

kindSymbols :: TraverseKind -> String
kindSymbols = \case
  ParK -> "{ ... }"
  TenK -> "[ ... ]"
  SeqK -> "[: ... :]"

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

litR :: Integer -> RFactor
litR = RFactor . Lit . LInteger

int0, int1 :: Term
int0 = Lit (LInteger 0)
int1 = Lit (LInteger 1)

multTerm :: Term -> Term -> Term
multTerm x y
  | x == int0 || y == int0 = int0
  | x == int1              = y
  | y == int1              = x
  | Lit (LInteger i) <- x
  , Lit (LInteger j) <- y  = Lit (LInteger $ i * j)
  | otherwise              = Def multName [x,y]

instance Monoid RFactor where
  mempty = litR 1
  mappend (RFactor x) (RFactor y) = RFactor (multTerm x y)

isLitR :: RFactor -> Maybe Integer
isLitR (RFactor (Lit (LInteger i))) = Just i
isLitR _                            = Nothing

isAddR :: RFactor -> Maybe (RFactor, RFactor)
isAddR (RFactor (Def ((== addName)->True) [x, y])) = Just (RFactor x, RFactor y)
isAddR _ = Nothing
