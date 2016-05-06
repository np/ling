{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Ling.Rename where

import           Control.Lens
import           Ling.Free
import           Ling.Norm
import           Ling.Prelude

data Ren = Ren { _renName  :: Ren -> Endom Name
               , _bndNames :: Set Name
               , _bndChans :: Set Channel
               }

makeLenses ''Ren

instance Monoid Ren where
  mempty = Ren (const id) ø ø
  Ren f x y `mappend` Ren g z t = Ren (\ren -> f ren . g ren) (x <> y) (z <> t)

inRen :: Name -> Ren -> Bool
x `inRen` ren = ren ^. bndNames . hasKey x || ren ^. bndChans . hasKey x

boundNames :: Fold s Name -> s -> Endom Ren
boundNames f s = bndNames <>~ setOf f s

boundChans :: Fold s Channel -> s -> Endom Ren
boundChans f s = bndChans <>~ setOf f s

-- `rename1 (x,y) s` replaces *all* the occurrences of `x` in `s`
-- and put `y` instead.
rename1 :: Rename a => (Name, Name) -> Endom a
rename1 xy = rename $ Ren (const $ subst1 xy id) ø ø

suffixingBy :: String -> Ren
suffixingBy suff = Ren f ø ø
  where
    f ren x
      -- This is not necessarily good since one might want to make all the
      -- names non-anon internally.
      | x == anonName = x
      | x `inRen` ren = suffixedName suff # x
      | otherwise     = x

hDef :: Name -> Maybe Typ -> Term -> (Name, Maybe Typ, Term)
hDef x mty tm = (hx, hmty, htm)
  where
    r    = suffixingBy (unName # x)
    hmty = rename r mty
    htm  = rename r tm
    hx   = internalNameFor htm # x

hDec :: Dec -> Dec
hDec = \case
  dec@Dat{}     -> dec
  dec@Assert{}  -> dec
  Sig x mty mtm ->
    let r = suffixingBy (unName # x) in
    Sig x (rename r mty) (rename r mtm)

class Rename a where
  rename :: Ren -> Endom a

instance Rename Name where
  rename f = (f ^. renName) f

instance Rename Term where
  rename f = \case
    Def x es   -> Def (rename f x) (rename f es)
    Let defs t -> Let (rename f defs) (rename (boundNames (defsMap . to keys . each) defs f) t)
    Lam arg t  -> Lam (rename f arg) (rename (boundNames argName arg f) t)
    TFun arg t -> TFun (rename f arg) (rename (boundNames argName arg f) t)
    TSig arg t -> TSig (rename f arg) (rename (boundNames argName arg f) t)
    Con x      -> Con (rename f x)
    Case t brs -> Case (rename f t) (rename f brs)
    e0@TTyp    -> e0
    e0@Lit{}   -> e0
    Proc cs p  -> Proc (rename f cs) (rename (boundChans (to bcChanDecs . folded) cs f) p)
    TProto rs  -> TProto (rename f rs)
    TSession s -> TSession (rename f s)

instance Rename Defs where
  rename = over each . rename

instance (Rename a, Rename b) => Rename (Ann a b) where
  rename f = bimap (rename f) (rename f)

instance Rename a => Rename (Arg a) where
  rename f (Arg x e) = Arg (rename (boundNames id x f) x) (rename f e)

instance Rename a => Rename [a] where
  rename = map . rename

instance Rename a => Rename (Maybe a) where
  rename = fmap . rename

instance (Rename a, Rename b) => Rename (a, b) where
  rename f = bimap (rename f) (rename f)

instance Rename ChanDec where
  rename f (ChanDec c r os) = ChanDec (rename (boundChans id c f) c) (rename f r) (rename f os)

-- This instance is reserved for CPatt used in a binding position
instance Rename CPatt where
  rename f = \case
    ChanP cd    -> ChanP (rename f cd)
    ArrayP k ps -> ArrayP k (rename f ps)

renameAtCPatt :: Ren -> Endom CPatt
renameAtCPatt f = \case
  ChanP cd    -> ChanP (renameAtChanDec f cd)
  ArrayP k ps -> ArrayP k (renameAtCPatt f <$> ps)

renameAtChanDec :: Ren -> Endom ChanDec
renameAtChanDec f (ChanDec c r os) =
  ChanDec (rename f c) (rename f r) (rename f os)

instance Rename NewPatt where
  rename f = \case
    NewChans k cs -> NewChans k (rename f cs)
    NewChan c os  -> NewChan (rename f c) (rename f os)

instance Rename Act where
  rename f = \case
    Split c pat     -> Split (rename f c) (rename f pat)
    Send c os e     -> Send (rename f c) (rename f os) (rename f e)
    Recv c arg      -> Recv (rename f c) (rename f arg)
    Nu ann newpatt  -> Nu (rename f ann) (rename f newpatt)
    Ax s cs         -> Ax (rename f s) (rename f cs)
    At t cs         -> At (rename f t) (renameAtCPatt f cs)
    LetA defs       -> LetA (rename f defs)

instance Rename Proc where
  rename f = \case
    Act act ->
      Act (rename f act)
    proc0 `Dot` proc1 ->
      rename f proc0 `Dot`
        rename (boundChans (to bcProc . folded) proc0 $
                boundNames (to bvProc . folded) proc0 f) proc1
    Procs procs ->
      Procs (rename f procs)
    NewSlice cs t x proc0 ->
      NewSlice (rename f cs) (rename f t)
               (rename (boundNames id x f) x) (rename (boundNames id x f) proc0)

instance Rename a => Rename (Prll a) where
  rename = over unPrll . rename

instance Rename Session where
  rename f = \case
    Array k ss -> Array k (rename f ss)
    IO p arg s -> IO p (rename f arg) (rename (boundNames argName arg f) s)
    TermS p t  -> TermS p (rename f t)

instance Rename RSession where
  rename f (Repl s t) = Repl (rename f s) (rename f t)

instance Rename RFactor where
  rename f (RFactor t) = RFactor (rename f t)
