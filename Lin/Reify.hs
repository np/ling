{-# LANGUAGE TypeFamilies #-}
module Lin.Reify where

import Prelude hiding (log)
import Lin.Abs
import Lin.Utils
import Lin.Session
import Lin.Proc
import qualified Lin.Norm as N

normOp :: Op -> Name
normOp Plus = Name "_+_"

class Norm a where
  type Normalized a
  norm  :: a -> Normalized a
  reify :: Normalized a -> a

{-
class Reify a where
  type Reified a
  reify :: a -> Reified a
  norm  :: Reified a -> a
-}

instance Norm a => Norm [a] where
  type Normalized [a] = [Normalized a]
  reify = map reify
  norm  = map norm

instance Norm Session where
  type Normalized Session = N.Session
  reify (N.Par s)   = Par (reify s)
  reify (N.Ten s)   = Ten (reify s)
  reify (N.Seq s)   = Seq (reify s)
  reify (N.Snd a s) = Snd (reify a) (reify s)
  reify (N.Rcv a s) = Rcv (reify a) (reify s)
  reify N.End       = End

  norm (Par s)    = N.Par (norm s)
  norm (Ten s)    = N.Ten (norm s)
  norm (Seq s)    = N.Seq (norm s)
  norm (Snd a s)  = N.Snd (norm a) (norm s)
  norm (Rcv a s)  = N.Rcv (norm a) (norm s)
  norm (Loli s t) = N.Par $ list [dual (norm s), norm t]
  norm (Dual s)   = dual (norm s)
  norm (Log s)    = log (norm s)
  norm (Fwd n s)
    | n >= 0 && n < 10000 = fwd (fromInteger n) (norm s)
    | otherwise           = error "Do you really want to blow the stack?"
  norm End        = N.End
  norm (Sort a e) = sort (norm a) (norm e)

instance Norm CSession where
  type Normalized CSession = N.Session
  reify N.End   = Done
  reify s       = Cont (reify s)
  norm  Done    = N.End
  norm (Cont s) = norm s

reifySession :: N.Session -> Session
reifySession = reify

reifySessions :: [N.Session] -> [Session]
reifySessions = reify

instance Norm RSession where
  type Normalized RSession = N.RSession
  reify (N.Repl s (N.Lit 1)) = Repl (reify s) One
  reify (N.Repl s t)         = Repl (reify s) (Some (reify t))
  norm  (Repl s One)         = one (norm s)
  norm  (Repl s (Some a))    = N.Repl (norm s) (norm a)

reifyRSession :: N.RSession -> RSession
reifyRSession = reify

reifyRSessions :: [N.RSession] -> [RSession]
reifyRSessions = reify

instance Norm Proc where
  type Normalized Proc = N.Proc
  reify (N.Act prefs procs) = Act (reify prefs) (reify procs)
  reify (N.Ax s c d es)     = Act [] (Ax (reify s) c d (reify es))
  reify (N.At t cs)         = Act [] (At (reify t) cs)
  norm  (Act   prefs procs) = N.Act (norm  prefs) (norm  procs)

reifyProc :: N.Proc -> Proc
reifyProc = reify

instance Norm Procs where
  type Normalized Procs = N.Procs
  reify []              = ZeroP
  reify procs           = Procs (reify procs)
  norm ZeroP            = []
  norm (Procs procs)    = norm procs
--norm (Ax s c d es)    = [N.Ax (norm s) c d (norm es)]
  norm (Ax s c d es)    = [fwdP (norm s) c d (norm es)]
  norm (At t cs)        = [N.At (norm t) cs]

instance Norm Snk where
  type Normalized Snk = Channel
  reify               = Snk
  norm (Snk c)        = c

instance Norm Pref where
  type Normalized Pref = N.Pref
  reify e = case e of
    N.Nu c d        -> Nu (reify c) (reify d)
    N.ParSplit c ds -> ParSplit c (reify ds)
    N.TenSplit c ds -> TenSplit c (reify ds)
    N.Send     c t  -> Send     c (reify t)
    N.Recv     c a  -> Recv     c (reify a)
    N.NewSlice t x  -> NewSlice (reify t) x

  norm  e = case e of
    Nu c d        -> N.Nu (norm c) (norm d)
    ParSplit c ds -> N.ParSplit c (norm ds)
    TenSplit c ds -> N.TenSplit c (norm ds)
    Send     c t  -> N.Send     c (norm t)
    Recv     c a  -> N.Recv     c (norm a)
    NewSlice t x  -> N.NewSlice (norm t) x

reifyPref :: N.Pref -> Pref
reifyPref = reify

{-
-- isInfix xs = match "_[^_]*_" xs
isInfix (Name('_':xs@(_:_))) = last xs == '_' && '_' `notElem` init xs
isInfix _                    = False
-}
isInfix :: Name -> Maybe Op
isInfix (Name "_+_") = Just Plus
isInfix _            = Nothing

instance Norm Term where
  type Normalized Term = N.Term

  reify e0 = case e0 of
    N.Def x []         -> Var x
    N.Def x [e1,e2]     | Just op <- isInfix x
                       -> Infix (reify e1) op (reify e2)
    N.Def x es         -> Def x (reify es)
    N.Lit n            -> Lit n
    N.Proc cs p        -> Proc (reify cs) (reify p)
    N.Ann e typ        -> EAnn (reify e) (reify typ)
    N.TTyp             -> TTyp
    N.TFun (Arg a t) s -> TFun (VarDec a (reify t)) [] (reify s)
    N.TSig (Arg a t) s -> TSig (VarDec a (reify t)) [] (reify s)
    N.TProto ss        -> TProto (reify ss)

  norm (Var x)          = N.Def x []
  norm (Infix e0 op e1) = N.Def (normOp op) [norm e0, norm e1]
  norm (Def x es)       = N.Def x (norm es)
  norm (Lit n)          = N.Lit n
  norm (Proc cs p)      = N.Proc (norm cs) (norm p)
  norm (EAnn e typ)     = N.Ann (norm e) (normType typ)
  norm TTyp             = N.TTyp
  norm (TFun xs xss t)  = normTele N.TFun (xs:xss) (normType t)
  norm (TSig xs xss t)  = normTele N.TSig (xs:xss) (normType t)
  norm (TProto ss)      = N.TProto (norm ss)

reifyTerm :: N.Term -> Term
reifyTerm = reify

instance Norm ChanDec where
  type Normalized ChanDec = N.ChanDec
  reify (Arg c s)         = ChanDec c (reify s)
  norm  (ChanDec c s)     = Arg c (norm s)

instance Norm VarDec where
  type Normalized VarDec = N.VarDec
  reify (Arg x s)        = VarDec x (reify s)
  norm  (VarDec x s)     = Arg x (norm s)

instance Norm OptSession where
  type Normalized OptSession = Maybe N.Session
  reify (Just s)     = SoSession (reify s)
  reify Nothing      = NoSession
  norm NoSession     = Nothing
  norm (SoSession s) = Just (norm s)

normTele :: (Arg N.Typ -> N.Typ -> N.Typ) -> [VarDec] -> N.Typ -> N.Typ
normTele f xs z = foldr (f . norm) z xs

normType :: Term -> N.Typ
normType t = case t of
  Lit{}  -> error "normType: a literal cannot be a type"
  Proc{} -> error "normType: a process cannot be a type"
  _      -> norm t

instance Norm OptChanDecs where
  type Normalized OptChanDecs = [N.ChanDec]
  reify []   = NoChanDecs
  reify decs = SoChanDecs (reify decs)

  norm NoChanDecs        = []
  norm (SoChanDecs decs) = norm decs

instance Norm Program where
  type Normalized Program = N.Program
  reify (N.Program decs)  =   Program (reify decs)
  norm  (Program   decs)  = N.Program (norm  decs)

reifyProgram :: N.Program -> Program
reifyProgram = reify

instance Norm Dec where
  type Normalized Dec  = N.Dec
  reify (N.Sig d t)    =   Sig d (reify t)
  reify (N.Dec d cs p) =   Dec d (reify cs) (reify p)
  norm  (Sig   d t)    = N.Sig d (norm t)
  norm  (Dec   d cs p) = N.Dec d (norm cs) (norm p)

-- -}
