{-# LANGUAGE FlexibleInstances            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving   #-}
{-# LANGUAGE LambdaCase                   #-}
{-# LANGUAGE MultiParamTypeClasses        #-}
{-# LANGUAGE Rank2Types                   #-}
{-# LANGUAGE TemplateHaskell              #-}
{-# LANGUAGE TypeFamilies                 #-}
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

data ChanDec = ChanDec { _cdChan :: !Channel
                       , _cdRepl :: !RFactor
                       , _cdSession :: !(Maybe RSession)
                       }
  deriving (Eq,Ord,Show,Read)

type VarDec  = Arg (Maybe Typ)

data Program = Program { _prgDecs :: ![Dec] }
  deriving (Eq,Ord,Show,Read)

data Dec
  = Sig { _decName :: !Name, _decType :: !(Maybe Typ), _decTerm :: !Term }
  | Dat { _decName :: !Name, _decConstructors :: ![Name] }
  | Assert { _decAssertion :: !Assertion }
  deriving (Eq,Ord,Show,Read)

data Assertion
  = Equal { _assertLeft, _assertRight :: !Term, _assertType :: !(Maybe Typ) }
  deriving (Eq,Ord,Show,Read)

infixr 4 `Dot`

-- See `Ling.WellFormed` for the conditions on Proc
data Proc
  = Act { _procAct :: !Act }
  | LetP { _letPDefs :: !Defs, _letPProc :: Proc }
  | Procs { _procProcs :: !(Prll Proc) }
  | Dot { _procDotL, _procDotR :: Proc }
  | NewSlice ![Channel] !RFactor !Name Proc
  deriving (Eq,Ord,Show,Read)

type Pref  = Prll Act
type Procs = Prll Proc

data TraverseKind
  = ParK
  | TenK
  | SeqK
  deriving (Eq,Ord,Show,Read,Enum)

data CPatt
    = ChanP  { _cpChanDec :: !ChanDec }
    | ArrayP { _cpArrayKind :: !TraverseKind
             , _cpPatts :: ![CPatt] }
  deriving (Eq, Ord, Show, Read)

data NewPatt
  = NewChans { _newKind :: !TraverseKind
             , _newChans :: ![ChanDec] }
  | NewChan  { _newChan :: !Channel
             , _newSig  :: !(Maybe Typ) }
  deriving (Eq, Ord, Show, Read)

data Act
  = Nu       { _newAnns :: ![Term]
             , _newPatt :: !NewPatt }
  | Split    { _actChan :: !Channel
             , _actPatt :: !CPatt }
  | Send     { _actChan :: !Channel
             , _actMSes :: !(Maybe Session)
             , _actTerm :: !Term }
  | Recv     { _actChan :: !Channel
             , _actVarD :: !VarDec }
  | Ax       { _actSess :: !Session -- Maybe
             , _axChans :: ![Channel] }
  | At       { _actTerm :: !Term
             , _actPatt :: !CPatt }
  deriving (Eq,Ord,Show,Read)

type DataTypeName = Name
type ConName = Name
type Branch = (ConName,Term)

data DefKind
  = Undefined
  | Defined
  deriving (Eq,Ord,Show,Read)

type Typ = Term
data Term
  = Def { _tmDefKind :: !DefKind, _tmVar :: !Name, _tmArgs :: ![Term] }
  | Let { _tmDefs :: !Defs, _tmTerm :: Term }
  | Lit { _tmLit :: !Literal }
  | Lam { _tmVarD :: !VarDec
        , _tmTerm :: Term }
  | Con { _tmCon :: !ConName }
  | Case { _tmCasee    :: Term
         , _tmBranches :: ![Branch]
         -- ^ Sorted
         }
  | Proc { _tmBndChans :: ![ChanDec]
         , _tmProc :: !Proc }
  | TTyp
  | TFun { _tmVarD :: !VarDec
         , _tmTerm :: Term }
  | TSig { _tmVarD :: !VarDec
         , _tmTerm :: Term }
  | TProto { _tmSessions :: !Sessions }
  | TSession !Session -- tSession is used instead of _tmSession
  deriving (Eq,Ord,Show,Read)

tSession :: Iso' Session Term
tSession = iso fwd bkd
  where
    fwd (TermS so t) | so == idOp = t
    fwd           s  = TSession s
    bkd (TSession s) = s
    bkd           t  = TermS idOp t

-- Polarity with a read/write (recv/send) flavor
data RW = Read | Write
  deriving (Eq,Ord,Show,Read,Enum)

data SessionOp = SessionOp { _rwOp :: !(FinEndom RW), _arrayOp :: !(FinEndom TraverseKind) }
  deriving (Eq,Ord,Show,Read)

idOp :: SessionOp
idOp = SessionOp idEndom idEndom

data Session
  = TermS { _sSessionOp :: !SessionOp, _sTerm :: !Term }
  | IO { _ioRW :: !RW, _ioVarD :: !VarDec, _ioSession :: Session }
  | Array { _arrayKind :: !TraverseKind, _arraySessions :: !Sessions }
  deriving (Eq,Ord,Show,Read)

depSend, depRecv :: VarDec -> Endom Session
depSend = IO Write
depRecv = IO Read

sendS, recvS :: Typ -> Endom Session
sendS = depSend . anonArg . Just
recvS = depRecv . anonArg . Just

data RSession
  = Repl { _rsession :: !Session
         , _rfactor  :: !RFactor
         }
  deriving (Eq,Ord,Show,Read)

newtype Sessions = Sessions [RSession]
  deriving (Eq,Ord,Show,Read,Monoid)

type NSession = Maybe Session

makeLenses ''Act
makeLenses ''Assertion
makeLenses ''ChanDec
makeLenses ''CPatt
makeLenses ''Dec
makeLenses ''Defs
makeLenses ''NewPatt
makeLenses ''Proc
makeLenses ''Program
makeLenses ''RFactor
makeLenses ''RSession
makeLenses ''Session
makeLenses ''Term
makePrisms ''Literal
makePrisms ''ChanDec
makePrisms ''Act
makePrisms ''NewPatt
makePrisms ''Assertion
makePrisms ''CPatt
makePrisms ''Dec
makePrisms ''Defs
makePrisms ''Proc
makePrisms ''Program
makePrisms ''RFactor
makePrisms ''RSession
makePrisms ''RW
makePrisms ''Session
makePrisms ''Sessions
makePrisms ''Term
makePrisms ''TraverseKind

aDef :: Name -> Maybe Typ -> Term -> Defs
aDef x mty tm
  | x == anonName = error $ "aDef: unexpected anon name `_` at type (" ++ ppShow mty ++ ") and definition (" ++ ppShow tm ++ ")"
  | otherwise     = _Wrapped . _Wrapped # [(x, Ann mty tm)]

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

instance t ~ Defs => Rewrapped Defs t
instance Wrapped Defs where
  type Unwrapped Defs = Map Name AnnTerm
  _Wrapped' = _Defs

instance Each Defs Defs (Arg AnnTerm) (Arg AnnTerm) where
  -- TODO,LENS: I would prefer to avoid the conversion to a list
  each = defsMap . _Wrapped . each . _Unwrapped

instance Monoid Program where
  mempty        = Program []
  mappend p0 p1 = Program $ p0^.prgDecs ++ p1^.prgDecs

instance Monoid Proc where
  mempty        = Procs ø
  mappend p0 p1 = mconcat ((p0,p1)^. both . to asProcs)
    where
      asProcs (Procs (Prll procs)) = procs
      asProcs p                    = [p]
  mconcat [p] = p
  mconcat ps  = Procs (Prll ps)

mkVar :: Name -> Term
mkVar n = Def Defined{-Var-} n []

-- Type constructors
mkTyCon :: Name -> [Term] -> Term
mkTyCon = Def Undefined

mkTyCon0 :: Name -> Term
mkTyCon0 n = mkTyCon n []

mkPrimOp :: Name -> [Term] -> Term
mkPrimOp = Def Undefined

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
  Just a  -> Def Defined (Name "_:_") [a,t]

vecTyp :: Typ -> Term -> Typ
vecTyp t e = mkTyCon (Name "Vec") [t,e]

intTyp :: Typ
intTyp = mkTyCon0 (Name "Int")

doubleTyp :: Typ
doubleTyp = mkTyCon0 (Name "Double")

stringTyp :: Typ
stringTyp = mkTyCon0 (Name "String")

charTyp :: Typ
charTyp = mkTyCon0 (Name "Char")

sessionTyp :: Typ
sessionTyp = mkTyCon0 (Name "Session")

allocationTyp :: Typ
allocationTyp = mkTyCon0 (Name "Allocation")

addName :: Name
addName = Name "_+_"

multName :: Name
multName = Name "_*_"

-- WARNING: this does not include `let` definitions, these
-- should be handled with their definitions.
actVarDecs :: Act -> [VarDec]
actVarDecs = \case
  Recv _ a       -> [a]
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

actLabel :: Act -> String
actLabel = \case
  Nu{}    -> "new"
  Split{} -> "split"
  Send{}  -> "send"
  Recv{}  -> "recv"
  Ax{}    -> "fwd"
  At{}    -> "@"

isSendRecv :: Act -> Bool
isSendRecv = \case
  Recv{}     -> True
  Send{}     -> True
  Split{}    -> False
  Nu{}       -> False
  Ax{}       -> False
  At{}       -> False

allSndRcv :: Session -> Bool
allSndRcv = \case
  IO _ _ s              -> allSndRcv s
  Array _ (Sessions []) -> True
  _                     -> False


type Brs a = [(ConName, a)]

branches :: Traversal (Brs a) (Brs b) a b
branches = traverse . _2

data CaseView a
  = NoCase a
  -- ^ One branch has matched so this is not a `case` anymore.
  --   Or all the branches where equivalent so a/the branch was selected.
  | SoCase { _caseOf :: Term, _caseBrs :: Brs a }

makeLenses ''CaseView

unCaseView :: CaseView Term -> Term
unCaseView = \case
  NoCase t     -> t
  SoCase t brs -> Case t brs

instance Functor CaseView where
  fmap f = \case
    NoCase x     -> NoCase (f x)
    SoCase t brs -> SoCase t (brs & branches %~ f)

type MkCase a b = Term -> Brs a -> b
type MkCase' a = MkCase a a

mkCaseViewBy :: Rel a -> MkCase a (CaseView a)
mkCaseViewBy rel t brs
  | Con con <- t, Just rhs <- lookup con brs    = NoCase rhs
  | Just (_, s) <- theUniqBy (rel `on` snd) brs = NoCase s
  | otherwise                                   = SoCase t brs

mkCaseBy :: Rel Term -> MkCase' Term
mkCaseBy rel t = unCaseView . mkCaseViewBy rel t

mkCase :: MkCase' Term
mkCase = mkCaseBy (==)

mkCaseRSession :: Rel Term -> MkCase' RSession
mkCaseRSession rel u = repl . bimap h h . unzip . fmap unRepl
  where
    repl   (s, r)    = (s ^. from tSession) `Repl` (r ^. from rterm)
    unRepl (con, rs) = ((con, rs ^. rsession . tSession),
                        (con, rs ^. rfactor . rterm))
    h                = mkCaseBy rel u

mkCaseSessions :: Rel Term -> MkCase' Sessions
mkCaseSessions rel u brs =
  Sessions [mkCaseRSession rel u (brs & branches %~ unSingleton)]
  where
    unSingleton (Sessions [x]) = x
    unSingleton _              = error "mkCaseSessions"

int0, int1 :: Term
int0 = Lit (LInteger 0)
int1 = Lit (LInteger 1)

matchUndef2 :: Name -> Term -> Either Term (Term, Term)
matchUndef2 n = \case
  (Def Undefined d [x, y]) | d == n -> Right (x, y)
  r                                 -> Left r

addTerm :: Prism' Term (Term, Term)
addTerm = prism mk $ matchUndef2 addName
  where
    mk (x, y)
      | x == int0              = y
      | y == int0              = x
      | Lit (LInteger i) <- x
      , Lit (LInteger j) <- y  = Lit (LInteger $ i + j)
      | otherwise              = mkPrimOp addName [x,y]

multTerm :: Prism' Term (Term, Term)
multTerm = prism mk $ matchUndef2 multName
  where
    mk (x, y)
      | x == int0 || y == int0 = int0
      | x == int1              = y
      | y == int1              = x
      | Lit (LInteger i) <- x
      , Lit (LInteger j) <- y  = Lit (LInteger $ i * j)
      | otherwise              = mkPrimOp multName [x,y]

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

addDec :: Dec -> Endom Defs
addDec (Sig d mty tm) = at d ?~ Ann mty tm
addDec Dat{}          = id
addDec Assert{}       = id

transProgramDecs :: (Defs -> Endom Dec) -> Endom Program
transProgramDecs transDec (Program decs) = Program (mapAccumL go ø decs ^. _2)
  where
    go defs dec0 = (addDec dec1 defs, dec1)
      where
        dec1 = transDec defs dec0
