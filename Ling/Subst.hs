module Ling.Subst where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Bifunctor
import Control.Applicative
import Control.Lens

import Ling.Abs (Name)
import Ling.Utils
import Ling.Norm
-- import Ling.Print.Instances ()

type Sub = Map Name Term
type Defs = Sub

class Subst a where
  subst :: Sub -> a -> a

subst1 :: Subst a => (Name, Term) -> a -> a
subst1 = subst . l2m . pure

app :: Defs -> Term -> [Term] -> Term
app _    t []     = t
app defs t (u:us) = case unDef defs t of
                      Lam (Arg x _) t' -> app defs (subst1 (x,u) t') us
                      Def x es         -> Def x (es ++ us)
                      _                -> error "Ling.Subst.app: IMPOSSIBLE"

-- Spec: app0 = app Map.empty
app0 :: Term -> [Term] -> Term
app0 t []     = t
app0 t (u:us) = case t of
                  Lam (Arg x _) t' -> app0 (subst1 (x,u) t') us
                  Def x es         -> Def x (es ++ u:us)
                  _                -> error "Ling.Subst.app0: IMPOSSIBLE"

unDef :: Defs -> Term -> Term
unDef defs e0 =
  case e0 of
    Def x es -> fromMaybe e0 (app defs <$> defs ^. at x <*> pure es)
    _        -> e0

substName :: Sub -> Name -> Term
substName f x = fromMaybe (Def x []) (f ^. at x)

instance Subst Term where
  subst f e0 = case e0 of
    Def x es   -> app0 (substName f x) (subst f es)
    Lam  arg t -> Lam  (subst f arg) (subst (hideArg arg f) t)
    TFun arg t -> TFun (subst f arg) (subst (hideArg arg f) t)
    TSig arg t -> TSig (subst f arg) (subst (hideArg arg f) t)
    Case t brs -> Case (subst f t)   (map (second (subst f)) brs)
    Con{}      -> e0
    TTyp       -> e0
    Lit{}      -> e0

    Proc{}     -> error "subst/Proc: TODO"
    TProto{}   -> error "subst/TProto: TODO"

instance Subst a => Subst (Arg a) where
  subst f (Arg x e) = Arg x (subst f e)

instance Subst a => Subst [a] where
  subst = map . subst

instance Subst a => Subst (Maybe a) where
  subst = fmap . subst

type E a = a -> a

hideArg :: Arg a -> E Sub
hideArg (Arg x _) = Map.delete x

hidePref :: Pref -> E Sub
hidePref (Recv _ arg) = hideArg arg
hidePref _            = id

hidePrefs :: [Pref] -> E Sub
hidePrefs = flip (foldr hidePref)

instance Subst Pref where
  subst f pref = case pref of
    Split k c ds      -> Split k c (subst f ds)
    Send c e          -> Send c (subst f e)
    Recv c arg        -> Recv c (subst f arg)
    Nu c d            -> Nu (subst f c) (subst f d)

instance Subst Proc where
  subst f p0 = case p0 of
    Act prefs procs   -> Act (subst f prefs) (subst f procs)
    Ax{}              -> p0
    At t cs           -> At (subst f t) cs
    NewSlice cs t x p -> NewSlice cs (subst f t) x (subst (Map.delete x f) p)

instance Subst Session where
  subst f s0 = case s0 of
    Ten ss  -> Ten (subst f ss)
    Par ss  -> Par (subst f ss)
    Seq ss  -> Seq (subst f ss)
    Snd t s -> Snd (subst f t) (subst f s)
    Rcv t s -> Rcv (subst f t) (subst f s)
    Atm{}   -> s0
    End     -> End

instance Subst RSession where
  subst f (Repl s t) = Repl (subst f s) (subst f t)
