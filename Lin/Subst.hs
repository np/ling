module Lin.Subst where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Applicative
import Control.Lens

import Lin.Abs (Name)
import Lin.Utils
import Lin.Norm
-- import Lin.Print.Instances ()

type Sub = Map Name Term

class Subst a where
  subst :: Sub -> a -> a

subst1 :: Subst a => (Name, Term) -> a -> a
subst1 = subst . l2m . pure

instance Subst Term where
  subst f e0 = case e0 of
    Def x es ->
     case (f ^. at x, es) of
       (Nothing, _)           -> Def x  (subst f es)
       (Just (Def x' es'), _) -> Def x' (es' ++ subst f es)
       (Just e', [])          -> e'
       (Just _e', _)          -> error $ "subst/Def " -- ++ pretty e' ++ " " ++ pretty es

    TFun arg t -> TFun (subst f arg) (subst (hideArg arg f) t)
    TSig arg t -> TSig (subst f arg) (subst (hideArg arg f) t)
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
hidePref (Recv _ arg)       = hideArg arg
hidePref _                  = id

hidePrefs :: [Pref] -> E Sub
hidePrefs = flip (foldr hidePref)

instance Subst Pref where
  subst f pref = case pref of
    Split k c ds      -> Split k c (subst f ds)
    Send c e          -> Send c (subst f e)
    Recv c arg        -> Recv c (subst f arg)
    Nu c d            -> Nu (subst f c) (subst f d)

instance Subst Proc where
  subst f p = case p of
    Act prefs procs   -> Act (subst f prefs) (subst f procs)
    Ax{}              -> p
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
