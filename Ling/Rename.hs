{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Ling.Rename where

import           Control.Lens
import           Ling.Norm
import           Ling.Prelude

data K = V | C | D
  deriving (Eq)

data Ren f = Ren { _renName  :: Ren f -> K -> EndoM f Name
                 , _bndVars  :: Set Name
                 , _bndChans :: Set Channel
                 }

makeLenses ''Ren

allNames :: Rename a => Fold a Name
allNames f = rename $ Ren (\_ _ -> f) ø ø

someNames :: Rename a => (forall f. Name -> Ren f -> K -> Bool) -> Fold a Name
someNames toKeep f = rename $ Ren g ø ø
  where
    g r k x | toKeep x r k = f    x
            | otherwise    = pure x

freeNames  :: Rename a => Fold a Name
freeVars   :: Rename a => Fold a Name
freeChans  :: Rename a => Fold a Channel
boundNames :: Rename a => Fold a Name
boundVars  :: Rename a => Fold a Name
boundChans :: Rename a => Fold a Channel

isBoundChan :: Channel -> Ren f -> K -> Bool
isBoundVar  :: Name    -> Ren f -> K -> Bool
isBoundName :: Name    -> Ren f -> K -> Bool
isFreeChan  :: Channel -> Ren f -> K -> Bool
isFreeVar   :: Name    -> Ren f -> K -> Bool
isFreeName  :: Name    -> Ren f -> K -> Bool

freeNames  = someNames isFreeName
freeVars   = someNames isFreeVar
freeChans  = someNames isFreeChan
boundNames = someNames isBoundName
boundVars  = someNames isBoundVar
boundChans = someNames isBoundChan

isBoundChan x ren k = k == C && ren ^. bndChans . hasKey x
isBoundVar  x ren k = k == V && ren ^. bndVars . hasKey x
isBoundName x ren k = isBoundVar x ren k || isBoundChan x ren k

isFreeChan x ren k = k == C && not (isBoundChan x ren k)
isFreeVar  x ren k = k == V && not (isBoundVar  x ren k)
isFreeName x ren k = k `elem` [C,V] && not (isBoundName x ren k)

markBoundVarsOf :: Fold s Name -> s -> Endom (Ren f)
markBoundVarsOf f s = bndVars <>~ setOf f s

markBoundVars :: Rename s => s -> Endom (Ren f)
markBoundVars = markBoundVarsOf boundVars

markBoundChansOf :: Fold s Channel -> s -> Endom (Ren f)
markBoundChansOf f s = bndChans <>~ setOf f s

markBoundChans :: Rename s => s -> Endom (Ren f)
markBoundChans = markBoundChansOf boundChans

-- `rename1 (x,y) s` replaces *all* the occurrences of `x` in `s`
-- and put `y` instead.
rename1 :: (Applicative f, Rename a) => (Name, Name) -> EndoM f a
rename1 xy = rename $ Ren (\_ _ -> pure . subst1 xy id) ø ø

rename1I :: Rename a => (Name, Name) -> Endom a
rename1I xy = runIdentity . rename1 xy

renameI :: Rename a => Ren Identity -> Endom a
renameI r = runIdentity . rename r

suffixingBy :: Applicative f => String -> Ren f
suffixingBy suff = Ren f ø ø
  where
    -- One might want to use k to show the kind of variables
    f ren k x
      -- This is not necessarily good since one might want to make all the
      -- names non-anon internally.
      | x == anonName       = pure x
      | isBoundName x ren k = pure $ suffixedName suff # x
      | otherwise           = pure x

hDef :: Name -> Maybe Typ -> Term -> (Name, Maybe Typ, Term)
hDef x mty tm
  | x == anonName = (anonName, mty, tm)
  | otherwise     = (hx, hmty, htm)
  where
    r    = suffixingBy (unName # x)
    hmty = renameI r mty
    htm  = renameI r tm
    hx   = internalNameFor htm # x

hDec :: Endom Dec
hDec = runIdentity . \case
  dec@Dat{}     -> pure dec
  dec@Assert{}  -> pure dec
  Sig x mty mtm ->
    let r = suffixingBy (unName # x) in
    Sig x <$> rename r mty <*> rename r mtm

class Rename a where
  rename :: Applicative f => Ren f -> EndoM f a

newtype FV = FV Name -- Free Var
newtype BV = BV Name -- Bound Var
newtype FC = FC Name -- Free Chan
newtype BC = BC Name -- Bound Chan
newtype DC = DC Name -- Data Constructor

makePrisms ''FV
makePrisms ''BV
makePrisms ''FC
makePrisms ''BC
makePrisms ''DC

instance Rename DC where rename f = _DC %%~ view renName f f D
instance Rename FV where rename f = _FV %%~ view renName f f V
instance Rename FC where rename f = _FC %%~ view renName f f C
instance Rename BV where rename f = _BV %%~ \n -> let g = markBoundVarsOf  id n f in view renName g g V n
instance Rename BC where rename f = _BC %%~ \n -> let g = markBoundChansOf id n f in view renName g g C n

instance Rename Term where
  rename f = \case
    Def x es   -> Def <$> from _FV (rename f) x <*> rename f es
    Let defs t -> Let <$> rename f defs <*> rename (markBoundVars defs f) t
    Lam arg t  -> Lam  <$> rename f arg <*> rename (markBoundVars arg f) t
    TFun arg t -> TFun <$> rename f arg <*> rename (markBoundVars arg f) t
    TSig arg t -> TSig <$> rename f arg <*> rename (markBoundVars arg f) t
    Con x      -> Con <$> from _DC (rename f) x
    Case t brs -> Case <$> rename f t <*> (each . bimapping (from _DC) id . rename) f brs
    e0@TTyp    -> pure e0
    e0@Lit{}   -> pure e0
    Proc cs p  -> Proc <$> rename f cs <*> rename (markBoundChans cs f) p
    TProto rs  -> TProto <$> rename f rs
    TSession s -> TSession <$> rename f s

instance Rename Defs where
  rename = each . rename

instance (Rename a, Rename b) => Rename (Ann a b) where
  rename f = bitraverse (rename f) (rename f)

instance Rename a => Rename (Arg a) where
  rename f (Arg x e) =
    Arg <$> from _BV (rename f) x <*> rename f e

instance Rename a => Rename [a] where
  rename = traverse . rename

instance Rename a => Rename (Maybe a) where
  rename = traverse . rename

instance (Rename a, Rename b) => Rename (a, b) where
  rename f = bitraverse (rename f) (rename f)

instance Rename ChanDec where
  rename f (ChanDec c r os) =
    ChanDec <$> from _BC (rename f) c <*> rename f r <*> rename f os

-- This instance is reserved for CPatt used in a binding position
instance Rename CPatt where
  rename f = \case
    ChanP cd    -> ChanP <$> rename f cd
    ArrayP k ps -> ArrayP k <$> rename f ps

renameAtCPatt :: Applicative f => Ren f -> EndoM f CPatt
renameAtCPatt f = \case
  ChanP cd    -> ChanP <$> renameAtChanDec f cd
  ArrayP k ps -> ArrayP k <$> each (renameAtCPatt f) ps

renameAtChanDec :: Applicative f => Ren f -> EndoM f ChanDec
renameAtChanDec f (ChanDec c r os) =
  ChanDec <$> from _FC (rename f) c <*> rename f r <*> rename f os

instance Rename NewPatt where
  rename f = \case
    NewChans k cs -> NewChans k <$> rename f cs
    NewChan c os  -> NewChan <$> from _BC (rename f) c <*> rename f os

instance Rename Act where
  rename f = \case
    Split c pat     -> Split <$> from _FC (rename f) c <*> rename f pat
    Send c os e     -> Send  <$> from _FC (rename f) c <*> rename f os <*> rename f e
    Recv c arg      -> Recv  <$> from _FC (rename f) c <*> rename f arg
    Nu ann newpatt  -> Nu    <$> rename f ann <*> rename f newpatt
    Ax s cs         -> Ax    <$> rename f s   <*> (each . from _FC . rename) f cs
    At t cs         -> At    <$> rename f t   <*> renameAtCPatt f cs

instance Rename Proc where
  rename f = \case
    Act act ->
      Act <$> rename f act
    proc0 `Dot` proc1 ->
      Dot <$> rename f proc0
          <*> rename (markBoundChans proc0 . markBoundVars proc0 $ f) proc1
    Procs procs ->
      Procs <$> rename f procs
    LetP defs proc0 ->
      LetP <$> rename f defs <*> rename (markBoundVars defs f) proc0
    NewSlice cs t x proc0 ->
      NewSlice <$> (each . from _FC . rename) f cs <*> rename f t
               <*> from _BV (rename f) x <*> rename (markBoundVars (BV x) f) proc0

instance Rename a => Rename (Prll a) where
  rename = _Prll . rename

instance Rename Session where
  rename f = \case
    Array k ss -> Array k <$> rename f ss
    IO p arg s -> IO p <$> rename f arg <*> rename (markBoundVars arg f) s
    TermS p t  -> TermS p <$> rename f t

instance Rename RSession where
  rename f (Repl s t) = Repl <$> rename f s <*> rename f t

instance Rename RFactor where
  rename = _RFactor . rename

instance Rename Sessions where
  rename = _Sessions . rename
