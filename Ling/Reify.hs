{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
module Ling.Reify where

import           Data.List
import           Ling.Abs
import qualified Ling.Norm    as N
import           Ling.Proc
import           Ling.Session
import           Ling.Utils
import           Prelude      hiding (log)

class Norm a where
  type Normalized a
  norm  :: a -> Normalized a
  reify :: Normalized a -> a

  normalize :: a -> a
  normalize = reify . norm

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
  norm (Sort a e) = sortSession (norm a) (norm e)

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

reifyDec :: N.Dec -> Dec
reifyDec = reify

instance Norm RSession where
  type Normalized RSession = N.RSession
  reify (N.Repl s (N.Lit (LInteger 1))) = Repl (reify s) One
  reify (N.Repl s t)                    = Repl (reify s) (Some (reify t))
  norm  (Repl s One)         = one (norm s)
  norm  (Repl s (Some a))    = N.Repl (norm s) (norm a)

reifyRSession :: N.RSession -> RSession
reifyRSession = reify

reifyRSessions :: [N.RSession] -> [RSession]
reifyRSessions = reify

instance Norm Proc where
  type Normalized Proc        = N.Proc
  reify (N.Dot pref procs)    = reifyPref pref (mkProcs $ reify procs)
  norm = \case
    PAct act        -> normAct act
    PNxt proc proc' -> norm proc `nxtP` norm proc'
    PDot proc proc' -> norm proc `dotP` asProcs (norm proc')
    PPrll procs     -> mconcat $ norm procs

mkProcs :: [Proc] -> Proc
mkProcs = \case
  []  -> PPrll []
  [p] -> p
  ps  -> PPrll ps

pAct :: N.Act -> Proc
pAct = PAct . reifyAct

pNxt :: Proc -> Proc -> Proc
pNxt proc0 (PPrll []) = proc0
pNxt proc0 proc1      = proc0 `PNxt` proc1

pDot :: Proc -> Proc -> Proc
pDot proc0 (PPrll []) = proc0
pDot proc0 proc1      = proc0 `PDot` proc1

actR :: N.Act -> Proc -> Proc
actR act proc
  | N.actNeedsDot act = pAct act `pDot` proc
  | otherwise         = pAct act `pNxt` proc

reifyPref :: N.Pref -> Proc -> Proc
reifyPref pref proc = case pref of
  []    -> proc
  [act] -> act `actR` proc
  acts  -> PPrll (map pAct acts) `pDot` proc

normAct :: Act -> N.Proc
normAct = \case
    -- These two clauses expand the forwarders
    Ax        s cs    -> fwdP      (norm s) cs
    SplitAx n s c     -> fwdProc n (norm s) c

    -- TODO make a flag to turn these on
{-
    Ax       s cs     -> go [ax               (norm s) cs]
    SplitAx  n s c    -> go (splitAx        n (norm s) c)
-}

    Nu c d            -> go [N.Nu (norm c) (norm d)]
    ParSplit c ds     -> go [N.Split N.ParK c (norm ds)]
    TenSplit c ds     -> go [N.Split N.TenK c (norm ds)]
    SeqSplit c ds     -> go [N.Split N.SeqK c (norm ds)]
    Send     c t      -> go [N.Send         c (norm t)]
    Recv     c a      -> go [N.Recv         c (norm a)]
    NewSlice cs t x   -> go [N.NewSlice    cs (norm t) x]
    At       t cs     -> go [N.At             (norm t) cs]
  where go = (`actsP` [])

reifyProc :: N.Proc -> Proc
reifyProc = reify

reifyAct :: N.Act -> Act
reifyAct = \case
  N.Nu c d            -> Nu (reify c) (reify d)
  N.Split N.ParK c ds -> ParSplit c (reify ds)
  N.Split N.TenK c ds -> TenSplit c (reify ds)
  N.Split N.SeqK c ds -> SeqSplit c (reify ds)
  N.Send     c t      -> Send     c (reify t)
  N.Recv     c a      -> Recv     c (reify a)
  N.NewSlice cs t x   -> NewSlice cs (reify t) x
  N.Ax       s cs     -> Ax          (reify s) cs
  N.At       t cs     -> At          (reify t) cs

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
-- TODO:
--   * this only supports naive right-infix
--   * this currently fails to parse: `f x + y`
normRawApp :: [ATerm] -> N.Term
normRawApp [e] = norm e
normRawApp (e0 : Var (Name op) : es)
  | op `elem` ["-","+","*","/","-D","+D","*D","/D","++S"]
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
    N.Def x es -> DTTyp x (reify es)
    _          -> DTBnd (Name "_") (reify e0)

  norm (DTTyp x es) = N.Def x (norm es)
  norm (DTBnd (Name "_") e) = norm e
  norm  DTBnd{} = error "DTBnd..."

instance Norm ATerm where
  type Normalized ATerm = N.Term

  reify e0 = case e0 of
    N.Def x []         -> Var x
    N.Lit l            -> Lit l
    N.Con n            -> Con (reify n)
    N.TTyp             -> TTyp
    N.TProto ss        -> TProto (reify ss)
    _                  -> Paren (reify e0)

  norm (Var x)          = N.Def x []
  norm (Lit l)          = N.Lit l
  norm (Con n)          = N.Con (norm n)
  norm TTyp             = N.TTyp
  norm (TProto ss)      = N.TProto (norm ss)
  norm (Paren t)        = norm t

instance Norm Term where
  type Normalized Term = N.Term

  reify e0 = case e0 of
    N.Def x [e1,e2]     | Just op <- isInfix x
                       -> RawApp (reify e1) (Var op : reifyRawApp e2)
    N.Def x es         -> RawApp (Var x) (reify es)
    N.Lit l            -> RawApp (Lit l) []
    N.Con n            -> RawApp (Con (reify n)) []
    N.TTyp             -> RawApp  TTyp   []
    N.TProto ss        -> RawApp (TProto (reify ss)) []
    N.Proc cs p        -> TProc (reify cs) (reify p)
    N.Lam  (Arg a t) s -> Lam  (VD a (reify t)) [] (reify s)
    N.TFun (Arg a t) s -> TFun (VD a (reify t)) [] (reify s)
    N.TSig (Arg a t) s -> TSig (VD a (reify t)) [] (reify s)
    N.Case t brs       -> Case (reify t) (reify brs)

  norm (RawApp e es)    = normRawApp (e:es)
  norm (Case t brs)     = N.Case (norm t) (sort (norm brs))
  norm (TProc cs p)     = N.Proc (norm cs) (norm p)
  norm (Lam  xs xss t)  = normVarDec N.Lam  (xs:xss) (norm t)
  norm (TFun xs xss t)  = normVarDec N.TFun (xs:xss) (norm t)
  norm (TSig xs xss t)  = normVarDec N.TSig (xs:xss) (norm t)

instance Norm Branch where
  type Normalized Branch = (Name, N.Term)

  reify (n, t) = Br (reify n) (reify t)

  norm (Br n t) = (norm n, norm t)

instance Norm ConName where
  type Normalized ConName = Name
  reify = CN
  norm (CN n) = n

reifyTerm :: N.Term -> Term
reifyTerm = reify

instance Norm ChanDec where
  type Normalized ChanDec = N.ChanDec
  reify (Arg c s)         = CD c (reify s)
  norm  (CD c s)          = Arg c (norm s)

instance Norm VarDec where
  type Normalized VarDec = N.VarDec
  reify (Arg x s)        = VD x (reify s)
  norm  (VD x s)         = Arg x (norm s)

instance Norm OptSession where
  type Normalized OptSession = Maybe N.RSession
  reify (Just s)     = SoSession (reify s)
  reify Nothing      = NoSession
  norm NoSession     = Nothing
  norm (SoSession s) = Just (norm s)

normVarDec :: (Arg N.Term -> N.Term -> N.Term) -> [VarDec] -> N.Term -> N.Term
normVarDec f xs z = foldr (f . norm) z xs

instance Norm Program where
  type Normalized Program = N.Program
  reify (N.Program decs)  =   Prg     (reify decs)
  norm  (Prg       decs)  = N.Program (norm  decs)

reifyProgram :: N.Program -> Program
reifyProgram = reify

instance Norm OptSig where
  type Normalized OptSig = Maybe N.Term
  reify Nothing          = NoSig
  reify (Just t)         = SoSig (reify t)
  norm NoSig             = Nothing
  norm (SoSig t)         = Just (norm t)

instance Norm Dec where
  type Normalized Dec   = N.Dec

  norm  ( DSig d ty)    = N.Sig d (Just $ norm ty) Nothing
  norm  ( DDef d ty tm) = N.Sig d (norm ty) (Just $ norm tm)
  norm  ( DDat d cs)    = N.Dat d (norm cs)
  norm  ( AEq t1 t2 ty) = N.Equal (norm t1) (norm t2) (norm ty)

  reify (N.Sig _ Nothing   Nothing)   = error "IMPOSSIBLE Norm Dec/reify: no def nor sig"
  reify (N.Sig d (Just ty) Nothing)   = DSig d (reify ty)
  reify (N.Sig d ty        (Just tm)) = DDef d (reify ty) (reify tm)
  reify (N.Dat d cs)                  = DDat d (reify cs)
  reify (N.Equal t1 t2 ty)            = AEq (reify t1) (reify t2) (reify ty)

-- -}
