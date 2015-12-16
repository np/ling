{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Ling.Rename where

import           Control.Lens
import           Ling.Free
import           Ling.Norm
import           Ling.Prelude

data Ren = Ren { _renName  :: Endom Name
               , _renBound :: Set Name }

makeLenses ''Ren

class Rename a where
  rename :: Ren -> Endom a

-- `rename1 (x,y) s` replaces *all* the occurrences of `x` in `s`
-- and put `y` instead.
rename1 :: Rename a => (Name, Name) -> Endom a
rename1 xy = rename $ Ren (subst1 xy id) ø

instance Rename Name where
  rename = view renName

instance Rename Term where
  rename f = \case
    Def x es   -> Def (rename f x) (rename f es)
    Let defs t -> Let (rename f defs) (rename (bindersOf (defsMap . to keys . each) defs f) t)
    Lam arg t  -> Lam (rename f arg) (rename (bindersOf argName arg f) t)
    TFun arg t -> TFun (rename f arg) (rename (bindersOf argName arg f) t)
    TSig arg t -> TSig (rename f arg) (rename (bindersOf argName arg f) t)
    Con x      -> Con (rename f x)
    Case t brs -> Case (rename f t) (rename f brs)
    e0@TTyp    -> e0
    e0@Lit{}   -> e0
    Proc cs p  -> Proc (rename f cs) (rename f p)
    TProto rs  -> TProto (rename f rs)
    TSession s -> TSession (rename f s)

instance Rename Defs where
  rename = over defsMap . rename

instance (Rename a, Rename b) => Rename (Ann a b) where
  rename f = bimap (rename f) (rename f)

instance (Ord a, Rename a, Rename b) => Rename (Map a b) where
  rename f = l2m . rename f . m2l

instance Rename a => Rename (Arg a) where
  rename f (Arg x e) = Arg (rename f x) (rename f e)

instance Rename a => Rename [a] where
  rename = map . rename

instance Rename a => Rename (Maybe a) where
  rename = fmap . rename

instance (Rename a, Rename b) => Rename (a, b) where
  rename f = bimap (rename f) (rename f)

bindersOf :: Fold s Name -> s -> Endom Ren
bindersOf f s = renBound <>~ setOf f s

instance Rename ChanDec where
  rename f (ChanDec c r os) = ChanDec (rename f c) (rename f r) (rename f os)

instance Rename CPatt where
  rename f = \case
    ChanP cd    -> ChanP (rename f cd)
    ArrayP k ps -> ArrayP k (rename f ps)

instance Rename Act where
  rename f = \case
    Split k c ds    -> Split k (rename f c) (rename f ds)
    Send c e        -> Send (rename f c) (rename f e)
    Recv c arg      -> Recv (rename f c) (rename f arg)
    Nu ann k cs     -> Nu (rename f ann) k (rename f cs)
    Ax s cs         -> Ax (rename f s) (rename f cs)
    At t cs         -> At (rename f t) (rename f cs)
    LetA defs       -> LetA (rename f defs)

instance Rename Proc where
  rename f = \case
    Act act ->
      Act (rename f act)
    proc0 `Dot` proc1 ->
      rename f proc0 `Dot`
        rename (bindersOf (to bvProc . folded) proc0 f) proc1
    Procs procs ->
      Procs (rename f procs)
    NewSlice cs t x proc0 ->
      NewSlice (rename f cs) (rename f t) (rename f x) (rename f proc0)

instance Rename a => Rename (Prll a) where
  rename = over unPrll . rename

instance Rename Session where
  rename f = \case
    Array k ss -> Array k (rename f ss)
    IO p arg s -> IO p (rename f arg) (rename (bindersOf argName arg f) s)
    TermS p t  -> TermS p (rename f t)

instance Rename RSession where
  rename f (Repl s t) = Repl (rename f s) (rename f t)

instance Rename RFactor where
  rename f (RFactor t) = RFactor (rename f t)
