module Ling.Rename where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Control.Applicative
import Control.Lens

import Ling.Abs (Name)
import Ling.Utils
import Ling.Norm
-- import Ling.Print.Instances ()

type Ren = Map Name Name

type E a = a -> a

class Rename a where
  rename :: Ren -> E a

rename1 :: Rename a => (Name, Name) -> E a
rename1 = rename . l2m . pure

instance Rename Name where
  rename f n = fromMaybe n (f ^. at n)

instance Rename Term where
  rename f e0 = case e0 of
    Def x es   -> Def (rename f x) (rename f es)

    TFun arg t -> TFun (rename f arg) (rename (hideArg arg f) t)
    TSig arg t -> TSig (rename f arg) (rename (hideArg arg f) t)
    TTyp       -> e0
    Lit{}      -> e0

    Ann{}      -> error "rename/Ann: impossible"
    Proc{}     -> error "rename/Proc: TODO"
    TProto{}   -> error "rename/TProto: TODO"

instance Rename a => Rename (Arg a) where
  rename f (Arg x e) = Arg (rename f x) (rename f e)

instance Rename a => Rename [a] where
  rename = map . rename

instance Rename a => Rename (Maybe a) where
  rename = fmap . rename

hideArg :: Arg a -> E Ren
hideArg (Arg x _) = Map.delete x

hidePref :: Pref -> E Ren
hidePref (Recv _ arg)   = hideArg arg
hidePref (NewSlice _ x) = Map.delete x
hidePref _              = id

hidePrefs :: [Pref] -> E Ren
hidePrefs = flip (foldr hidePref)

instance Rename Pref where
  rename f pref = case pref of
    TenSplit c ds -> TenSplit (rename f c) (rename f ds)
    ParSplit c ds -> ParSplit (rename f c) (rename f ds)
    Send c e      -> Send (rename f c) (rename f e)
    Recv c arg    -> Recv (rename f c) (rename f arg)
    Nu c d        -> Nu (rename f c) (rename f d)
    NewSlice t x  -> NewSlice (rename f t) (rename f x)

instance Rename Proc where
  rename f (Act prefs procs) = Act (rename f prefs) (rename (hidePrefs prefs f) procs)
  rename f (Ax s c d es)     = Ax (rename f s) (rename f c) (rename f d) (rename f es)
  rename f (At t cs)         = At (rename f t) (rename f cs)

instance Rename Session where
  rename f s0 = case s0 of
    Ten ss  -> Ten (rename f ss)
    Par ss  -> Par (rename f ss)
    Seq ss  -> Seq (rename f ss)
    Snd t s -> Snd (rename f t) (rename f s)
    Rcv t s -> Rcv (rename f t) (rename f s)
    Atm p n -> Atm p (rename f n)
    End     -> End

instance Rename RSession where
  rename f (Repl s t) = Repl (rename f s) (rename f t)
