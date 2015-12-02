{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

module Ling.Subst where

import           Ling.Free
import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Scoped  hiding (subst1)
import           Ling.Session

class Subst a where
  subst :: Defs -> Endom a

subst1 :: Subst a => (Name, AnnTerm) -> Endom a
subst1 = subst . Defs . l2m . pure

substi :: (Integral i, Subst a) => (Name, i) -> Endom a
substi (x, i) = subst1 (x, Ann (Just intTyp) (litTerm . integral # i))

app :: Term -> [Term] -> Term
app t0 []     = t0
app t0 (u:us) =
  case t0 of
    Lam (Arg x mty) t1 -> app (subst1 (x, Ann mty u) t1) us
    Def x es           -> Def x (es ++ u : us)
    _                  -> error "Ling.Subst.app: IMPOSSIBLE"

unScoped :: Subst a => Scoped a -> a
unScoped s = subst (allDefs s) (s ^. scoped)

substName :: Defs -> Name -> Term
substName f x = f ^? at x . _Just . annotated ?| Def x []

-- TODO binder: make an instance for Abs and use it for Lam,TFun,TSig

instance Subst Term where
  subst f = \case
    Def x es   -> app (substName f x) (subst f es)
    Let defs t -> subst (defs <> f) t
    Lam arg t  -> Lam (subst f arg) (subst (hide argName arg f) t)
    TFun arg t -> TFun (subst f arg) (subst (hide argName arg f) t)
    TSig arg t -> TSig (subst f arg) (subst (hide argName arg f) t)
    Case t brs -> mkCase (subst f t) (second (subst f) <$> brs)
    e0@Con{}   -> e0
    e0@TTyp    -> e0
    e0@Lit{}   -> e0
    Proc cs p  -> Proc cs (subst f p)
    TProto rs  -> TProto (subst f rs)
    TSession s -> TSession (subst f s)

instance Subst a => Subst (Arg a) where
  subst f (Arg x e) = Arg x (subst f e)

instance Subst a => Subst [a] where
  subst = map . subst

instance Subst a => Subst (Maybe a) where
  subst = fmap . subst

instance (Subst a, Subst b) => Subst (a, b) where
  subst f = bimap (subst f) (subst f)

hide :: Fold s Name -> s -> Endom Defs
hide f = composeMapOf f sans

instance Subst Act where
  subst f = \case
    Split k c ds    -> Split k c (subst f ds)
    Send c e        -> Send c (subst f e)
    Recv c arg      -> Recv c (subst f arg)
    Nu c d          -> Nu (subst f c) (subst f d)
    NewSlice cs t x -> NewSlice cs (subst f t) x
    LetA{}          -> error "Subst/LetA"
    Ax s cs         -> Ax (subst f s) cs
    At t cs         -> At (subst f t) cs

instance Subst Proc where
  subst f (pref `Dot` procs) =
    subst f pref `Dot` subst (hide (to bvPref . folded) pref f) procs

instance Subst Session where
  subst f = \case
    Array k ss -> Array k (subst f ss)
    IO p arg s -> IO p (subst f arg) (subst (hide argName arg f) s)
    TermS p t  -> termS p (subst f t)

instance Subst RSession where
  subst f (Repl s t) = Repl (subst f s) (subst f t)

instance Subst RFactor where
  subst f (RFactor t) = RFactor (subst f t)
