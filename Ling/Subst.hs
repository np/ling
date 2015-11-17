{-# LANGUAGE LambdaCase #-}

module Ling.Subst where

import qualified Data.Map     as Map

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Scoped  hiding (subst1)
import           Ling.Session

class Subst a where
  subst :: Defs -> a -> a

subst1 :: Subst a => (Name, Term) -> a -> a
subst1 = subst . l2m . pure

substi :: (Integral i, Subst a) => (Name, i) -> a -> a
substi (x, i) = subst1 (x, Lit (LInteger (fromIntegral i)))

appG :: (Term -> Term) -> Term -> [Term] -> Term
appG g t [] = g t
appG g t (u:us) =
  case g t of
    Lam (Arg x _) t' -> appG g (subst1 (x, u) t') us
    Def x es         -> Def x (es ++ u : us)
    _                -> error "Ling.Subst.app: IMPOSSIBLE"

-- Spec: app0 = app Map.empty
app0 :: Term -> [Term] -> Term
app0 = appG id

{-
app0 t []     = t
app0 t (u:us) = case t of
                  Lam (Arg x _) t' -> app0 (subst1 (x,u) t') us
                  Def x es         -> Def x (es ++ u:us)
                  _                -> error "Ling.Subst.app0: IMPOSSIBLE"
-}
{-
unDef :: Defs -> Term -> Term
unDef defs e0 =
  case e0 of
    Def x es -> fromMaybe e0 (app <$> (Scoped defs <$> defs ^. at x) <*> pure es)
    _        -> e0
-}

unScoped :: Subst a => Scoped a -> a
unScoped s = subst (s ^. ldefs) (s ^. scoped)

substName :: Defs -> Name -> Term
substName f x = fromMaybe (Def x []) (f ^. at x)

-- TODO binder: make an instance for Abs and use it for Lam,TFun,TSig

instance Subst Term where
  subst f = \case
    Def x es   -> app0 (substName f x) (subst f es)
    Let defs t -> subst (defs `mergeDefs` f) t
    Lam arg t  -> Lam (subst f arg) (subst (hideArg arg f) t)
    TFun arg t -> TFun (subst f arg) (subst (hideArg arg f) t)
    TSig arg t -> TSig (subst f arg) (subst (hideArg arg f) t)
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

hideArg :: Arg a -> Endom Defs
hideArg (Arg x _) = Map.delete x

hideArgs :: [Arg a] -> Endom Defs
hideArgs = flip (foldr hideArg)

hidePref :: Pref -> Endom Defs
hidePref = hideArgs . concatMap actVarDecs

instance Subst Act where
  subst f = \case
    Split k c ds    -> Split k c (subst f ds)
    Send c e        -> Send c (subst f e)
    Recv c arg      -> Recv c (subst f arg)
    Nu c d          -> Nu (subst f c) (subst f d)
    NewSlice cs t x -> NewSlice cs (subst f t) x
    act@Ax{}        -> act
    At t cs         -> At (subst f t) cs

instance Subst Proc where
  subst f (pref `Dot` procs) =
    subst f pref `Dot` subst (hidePref pref f) procs

instance Subst Session where
  subst f = \case
    Array k ss -> Array k (subst f ss)
    IO p arg s -> IO p (subst f arg) (subst (hideArg arg f) s)
    TermS p t  -> termS p (subst f t)

instance Subst RSession where
  subst f (Repl s t) = Repl (subst f s) (subst f t)

instance Subst RFactor where
  subst f (RFactor t) = RFactor (subst f t)
