{-# LANGUAGE TypeFamilies #-}
module Lin.Reify where

import Prelude hiding (log)
import Lin.Abs
import Lin.Utils
import Lin.Session
import Lin.Proc
import qualified Lin.Norm as N

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

dualIfWrite :: N.RW -> Session -> Session
dualIfWrite N.Read  = id
dualIfWrite N.Write = Dual

instance Norm Session where
  type Normalized Session = N.Session
  reify (N.Par s)   = Par (reify s)
  reify (N.Ten s)   = Ten (reify s)
  reify (N.Seq s)   = Seq (reify s)
  reify (N.Snd a s) = Snd (reify a) (reify s)
  reify (N.Rcv a s) = Rcv (reify a) (reify s)
  reify (N.Atm p n) = dualIfWrite p (Atm n)
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
  norm (Atm n)    = N.Atm N.Read n -- Read is abitrary here
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
  type Normalized Proc        = N.Proc
  reify (N.Act prefs procs)   = Act (reify prefs) (reify procs)
  reify (N.Ax s c d es)       = Act [] (Ax (reify s) (c : d : es))
  reify (N.At t cs)           = Act [] (At (reify t) cs)
  reify (N.NewSlice cs t x p) = Act [] (NewSlice cs (reify t) x (reify p))
  norm  (Act prefs procs)     = N.Act (norm prefs) (norm procs)

reifyProc :: N.Proc -> Proc
reifyProc = reify

reifyProcs :: N.Procs -> Procs
reifyProcs ps = case reify ps of
  [Act [] ps'] -> ps'
  ps'          -> Procs ps'

instance Norm Procs where
  type Normalized Procs    = N.Procs
  reify []                 = ZeroP
  reify procs              = reifyProcs procs
  norm ZeroP               = []
  norm (Procs procs)       = norm procs
  norm (At t cs)           = [N.At (norm t) cs]
  norm (NewSlice cs t x p) = [N.NewSlice cs (norm t) x (norm p)]
  norm (Ax s es0)          =
    case es0 of
      c : d : es -> [fwdP (norm s) c d es]
                --  [N.Ax (norm s) c d es]
      _ -> error "Forwarders must be given at least two channels"

instance Norm Pref where
  type Normalized Pref = N.Pref
  reify e = case e of
    N.Nu c d            -> Nu (reify c) (reify d)
    N.Split N.ParK c ds -> ParSplit c (reify ds)
    N.Split N.TenK c ds -> TenSplit c (reify ds)
    N.Split N.SeqK c ds -> SeqSplit c (reify ds)
    N.Send     c t      -> Send     c (reify t)
    N.Recv     c a      -> Recv     c (reify a)

  norm  e = case e of
    Nu c d            -> N.Nu (norm c) (norm d)
    ParSplit c ds     -> N.Split N.ParK c (norm ds)
    TenSplit c ds     -> N.Split N.TenK c (norm ds)
    SeqSplit c ds     -> N.Split N.SeqK c (norm ds)
    Send     c t      -> N.Send         c (norm t)
    Recv     c a      -> N.Recv         c (norm a)

reifyPref :: N.Pref -> Pref
reifyPref = reify

-- isInfix xs = match "_[^_]*_" xs
isInfix :: Name -> Maybe Name
isInfix (Name('_':xs@(_:_:_)))
  | last xs == '_' && '_' `notElem` s
  = Just (Name s)
  where s = init xs
isInfix _ = Nothing

-- Really naive rawApp parsing
-- Next step is to carry an environment with
-- the operators and their fixity.
normRawApp :: [ATerm] -> N.Term
normRawApp [e] = norm e
normRawApp (e0 : Var (Name op) : es)
  | op `elem` ["-","+","*","/","-D","+D","*D","/D"]
  = N.Def (Name ("_" ++ op ++ "_")) [norm e0, normRawApp es]
normRawApp (Var x : es) = N.Def x (norm es)
normRawApp [] = error "normRawApp: IMPOSSIBLE"
normRawApp _ = error "normRawApp: unexpected application"

reifyRawApp :: N.Term -> [ATerm]
reifyRawApp e0 =
  case reify e0 of
    Paren (RawApp e1 es) -> e1 : es
    e0'                  -> [e0']

instance Norm DTerm where
  type Normalized DTerm = N.Term

  reify e0 = case e0 of
    N.Def x es -> DTerm x (reify es)
    _          -> error "DTerm.reify"

  norm (DTerm x es) = N.Def x (norm es)

instance Norm ATerm where
  type Normalized ATerm = N.Term

  reify e0 = case e0 of
    N.Def x []         -> Var x
    N.Lit n            -> Lit n
    N.TTyp             -> TTyp
    N.TProto ss        -> TProto (reify ss)
    _                  -> Paren (reify e0)

  norm (Var x)          = N.Def x []
  norm (Lit n)          = N.Lit n
  norm TTyp             = N.TTyp
  norm (TProto ss)      = N.TProto (norm ss)
  norm (Paren t)        = norm t

instance Norm Term where
  type Normalized Term = N.Term

  reify e0 = case e0 of
    N.Def x [e1,e2]     | Just op <- isInfix x
                       -> RawApp (reify e1) (Var op : reifyRawApp e2)
    N.Def x es         -> RawApp (Var x) (reify es)
    N.Lit n            -> RawApp (Lit n) []
    N.TTyp             -> RawApp  TTyp   []
    N.TProto ss        -> RawApp (TProto (reify ss)) []
    N.Proc cs p        -> Proc (reify cs) (reify p)
    N.TFun (Arg a t) s -> TFun (VarDec a (reify t)) [] (reify s)
    N.TSig (Arg a t) s -> TSig (VarDec a (reify t)) [] (reify s)

  norm (RawApp e es)    = normRawApp (e:es)
  norm (Proc cs p)      = N.Proc (norm cs) (norm p)
  norm (TFun xs xss t)  = normTele N.TFun (xs:xss) (norm t)
  norm (TSig xs xss t)  = normTele N.TSig (xs:xss) (norm t)

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
  type Normalized OptSession = Maybe N.RSession
  reify (Just s)     = SoSession (reify s)
  reify Nothing      = NoSession
  norm NoSession     = Nothing
  norm (SoSession s) = Just (norm s)

normTele :: (Arg N.Typ -> N.Typ -> N.Typ) -> [VarDec] -> N.Typ -> N.Typ
normTele f xs z = foldr (f . norm) z xs

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
