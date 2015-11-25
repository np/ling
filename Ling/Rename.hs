{-# LANGUAGE LambdaCase #-}

module Ling.Rename where

import           Ling.Norm
import           Ling.Prelude

type Ren = Name -> Name

class Rename a where
  rename :: Ren -> Endom a

rename1 :: Rename a => (Name, Name) -> Endom a
rename1 xy = rename (subst1 xy id)

instance Rename Name where
  rename = id

instance Rename Term where
  rename f = \case
    Def x es   -> Def (rename f x) (rename f es)
    Let defs t -> Let (rename f defs) (rename (hideDefs defs f) t)
    Lam arg t  -> Lam (rename f arg) (rename (hideArg arg f) t)
    TFun arg t -> TFun (rename f arg) (rename (hideArg arg f) t)
    TSig arg t -> TSig (rename f arg) (rename (hideArg arg f) t)
    Con x      -> Con (rename f x)
    Case t brs -> Case (rename f t) (rename f brs)
    e0@TTyp    -> e0
    e0@Lit{}   -> e0
    Proc cs p  -> Proc (rename f cs) (rename f p)
    TProto rs  -> TProto (rename f rs)
    TSession s -> TSession (rename f s)

instance Rename Defs where
  rename f = Defs . rename f . _defsMap

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

hideArg :: Arg a -> Endom Ren
hideArg (Arg x _) = hideName x

hideArgs :: [Arg a] -> Endom Ren
hideArgs = composeMapOf each hideArg

hideNames :: [Name] -> Endom Ren
hideNames = composeMapOf each hideName

hideDefs :: Defs -> Endom Ren
hideDefs = hideNames . keys . _defsMap

hidePref :: Pref -> Endom Ren
hidePref = hideArgs . concatMap actVarDecs

instance Rename CPatt where
  rename f = \case
    ChanP cd    -> ChanP (rename f cd)
    ArrayP k ps -> ArrayP k (rename f ps)

instance Rename Act where
  rename f = \case
    Split k c ds    -> Split k (rename f c) (rename f ds)
    Send c e        -> Send (rename f c) (rename f e)
    Recv c arg      -> Recv (rename f c) (rename f arg)
    Nu c d          -> Nu (rename f c) (rename f d)
    NewSlice cs t x -> NewSlice (rename f cs) (rename f t) (rename f x)
    Ax s cs         -> Ax (rename f s) (rename f cs)
    At t cs         -> At (rename f t) (rename f cs)
    LetA defs       -> LetA (rename f defs)

instance Rename Proc where
  rename f (pref `Dot` procs) =
    rename f pref `Dot` rename (hidePref pref f) procs

instance Rename Session where
  rename f = \case
    Array k ss -> Array k (rename f ss)
    IO p arg s -> IO p (rename f arg) (rename (hideArg arg f) s)
    TermS p t  -> TermS p (rename f t)

instance Rename RSession where
  rename f (Repl s t) = Repl (rename f s) (rename f t)

instance Rename RFactor where
  rename f (RFactor t) = RFactor (rename f t)
