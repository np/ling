{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE ViewPatterns    #-}
module Ling.Norm
  ( module Ling.Norm
  , Name(..)
  , Literal(..)
  ) where

import           Ling.Abs     (Literal (..), Name (Name))
import           Ling.Prelude

type AnnTerm = Ann (Maybe Typ) Term

newtype Defs = Defs { _defsMap :: Map Name AnnTerm }
  deriving (Eq, Ord, Read, Show)

newtype RFactor = RFactor { _rterm :: Term }
  deriving (Eq, Ord, Read, Show)

type ChanDec = Arg (Maybe RSession)
type VarDec  = Arg (Maybe Typ)

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
  | LetA     Defs
  deriving (Eq,Ord,Show,Read)

type DataTypeName = Name
type ConName = Name
type Branch = (ConName,Term)

type Typ = Term
data Term
  = Def Name [Term]
  | Let Defs Term
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
sendS = depSend . anonArg . Just
recvS = depRecv . anonArg . Just

data RSession
  = Repl { _rsession :: Session
         , _rfactor  :: RFactor
         }
  deriving (Eq,Ord,Show,Read)

type Sessions = [RSession]
type NSession = Maybe Session

makeLenses ''Defs
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

instance Monoid Defs where
  mempty = Defs ø
  mappend (Defs x) (Defs y) = Defs $ unionWithKey mergeDef x y
    where
      mergeDef k v w | v == w    = v
                     | otherwise = error $ "Scoped.mergeDefs: " ++ show k

type instance Index   Defs = Name
type instance IxValue Defs = AnnTerm

instance At Defs where
  at x = defsMap . at x

instance Ixed Defs where
  ix = ixAt

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
  NewSlice _ _ x -> [Arg x (Just intTyp)]
  LetA defs      -> [Arg x Nothing | x <- keys (defs ^. defsMap)]
  Nu{}           -> []
  Split{}        -> []
  Send{}         -> []
  Ax{}           -> []
  At{}           -> []

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
  LetA{}      -> "let"

actNeedsDot :: Act -> Bool
actNeedsDot = \case
  Nu{}       -> False
  Split{}    -> False
  Send{}     -> True
  Recv{}     -> True
  NewSlice{} -> True
  Ax{}       -> True
  At{}       -> True
  LetA{}     -> True

isSendRecv :: Act -> Bool
isSendRecv = \case
  Recv{}     -> True
  Send{}     -> True
  Split{}    -> False
  NewSlice{} -> False
  Nu{}       -> False
  Ax{}       -> False
  At{}       -> False
  LetA{}     -> False

allSndRcv :: Session -> Bool
allSndRcv = \case
  IO _ _ s   -> allSndRcv s
  Array _ [] -> True
  _          -> False


type Brs a = [(ConName, a)]

branches :: Traversal (Brs a) (Brs b) a b
branches = traverse . _2

type MkCase a = Term -> Brs a -> a

mkCaseBy :: Rel Term -> MkCase Term
mkCaseBy rel t brs
  | Con con <- t, Just rhs <- lookup con brs    = rhs
  | Just (_, s) <- theUniqBy (rel `on` snd) brs = s
  | otherwise                                   = Case t brs

mkCase :: MkCase Term
mkCase = mkCaseBy (==)

mkCaseRSession :: Rel Term -> MkCase RSession
mkCaseRSession rel u = repl . bimap h h . unzip . fmap unRepl
  where
    repl   (s, r)    = (s ^. from tSession) `Repl` (r ^. from rterm)
    unRepl (con, rs) = ((con, rs ^. rsession . tSession),
                        (con, rs ^. rfactor . rterm))
    h                = mkCaseBy rel u

mkCaseSessions :: Rel Term -> MkCase Sessions
mkCaseSessions rel u brs =
  [mkCaseRSession rel u (brs & branches %~ unSingleton)]
  where
    unSingleton [x] = x
    unSingleton _   = error "mkCaseSessions"

int0, int1 :: Term
int0 = Lit (LInteger 0)
int1 = Lit (LInteger 1)

matchDef2 :: Name -> Term -> Either Term (Term, Term)
matchDef2 n = \case
  (Def d [x, y]) | d == n -> Right (x, y)
  r                       -> Left r

addTerm :: Prism' Term (Term, Term)
addTerm = prism mk $ matchDef2 addName
  where
    mk (x, y)
      | x == int0              = y
      | y == int0              = x
      | Lit (LInteger i) <- x
      , Lit (LInteger j) <- y  = Lit (LInteger $ i + j)
      | otherwise              = Def addName [x,y]

multTerm :: Prism' Term (Term, Term)
multTerm = prism mk $ matchDef2 multName
  where
    mk (x, y)
      | x == int0 || y == int0 = int0
      | x == int1              = y
      | y == int1              = x
      | Lit (LInteger i) <- x
      , Lit (LInteger j) <- y  = Lit (LInteger $ i * j)
      | otherwise              = Def multName [x,y]

litTerm :: Prism' Term Integer
litTerm = prism (Lit . LInteger) $
  \case
    Lit (LInteger i) -> Right i
    t                -> Left  t

litR :: Prism' RFactor Integer
litR = rterm . litTerm

litR0, litR1 :: Prism' RFactor ()
litR0 = litR . only 0
litR1 = litR . only 1

addR :: Prism' RFactor (RFactor, RFactor)
addR = rterm . addTerm . (from rterm `bimapping` from rterm)

multR :: Prism' RFactor (RFactor, RFactor)
multR = rterm . multTerm . (from rterm `bimapping` from rterm)

instance Monoid RFactor where
  mempty      = litR # 1
  mappend x y = multR # (x, y)
