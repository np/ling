{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Ling.Rename where

import           Ling.Free
import           Ling.Norm
import           Ling.Prelude

type Ren = Endom Name

class Rename a where
  rename :: Ren -> Endom a

rename1 :: Rename a => (Name, Name) -> Endom a
rename1 xy = rename (subst1 xy id)

instance Rename Name where
  rename = id

instance Rename Term where
  rename f = \case
    Def x es   -> Def (rename f x) (rename f es)
    Let defs t -> Let (rename f defs) (rename (hide (defsMap . to keys . each) defs f) t)
    Lam arg t  -> Lam (rename f arg) (rename (hide argName arg f) t)
    TFun arg t -> TFun (rename f arg) (rename (hide argName arg f) t)
    TSig arg t -> TSig (rename f arg) (rename (hide argName arg f) t)
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

hideName :: Name -> Endom Ren
hideName x f y | x == y    = y
               | otherwise = f y

hide :: Fold s Name -> s -> Endom Ren
hide f = composeMapOf f hideName

instance Rename CPatt where
  rename f = \case
    ChanP cd    -> ChanP (rename f cd)
    ArrayP k ps -> ArrayP k (rename f ps)

instance Rename Act where
  rename f = \case
    Split k c ds    -> Split k (rename f c) (rename f ds)
    Send c e        -> Send (rename f c) (rename f e)
    Recv c arg      -> Recv (rename f c) (rename f arg)
    Nu ann cs       -> Nu (rename f ann) (rename f cs)
    Ax s cs         -> Ax (rename f s) (rename f cs)
    At t cs         -> At (rename f t) (rename f cs)
    LetA defs       -> LetA (rename f defs)

instance Rename Proc where
  rename f = \case
    Act act ->
      Act (rename f act)
    proc0 `Dot` proc1 ->
      rename f proc0 `Dot`
        rename (hide (to bvProc . folded) proc0 f) proc1
    Procs procs ->
      Procs (rename f procs)
    NewSlice cs t x proc0 ->
      NewSlice (rename f cs) (rename f t) (rename f x) (rename f proc0)

instance Rename a => Rename (Prll a) where
  rename = over unPrll . rename

instance Rename Session where
  rename f = \case
    Array k ss -> Array k (rename f ss)
    IO p arg s -> IO p (rename f arg) (rename (hide argName arg f) s)
    TermS p t  -> TermS p (rename f t)

instance Rename RSession where
  rename f (Repl s t) = Repl (rename f s) (rename f t)

instance Rename RFactor where
  rename f (RFactor t) = RFactor (rename f t)
