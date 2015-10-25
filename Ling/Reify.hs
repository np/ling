{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
module Ling.Reify where

import           Data.List
import           Ling.Raw
import qualified Ling.Norm    as N
import           Ling.Proc
import           Ling.Session
import           Ling.Utils
import           Prelude      hiding (log)

newtype RawSession = RawSession { rawSession :: Term }

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

instance Norm CSession where
  type Normalized CSession = N.Session
  reify s | s == endS = Done
          | otherwise = Cont . rawSession $ reify s
  norm  Done    = endS
  norm (Cont s) = norm (RawSession s)

instance Norm ASession where
  type Normalized ASession = N.Session
  norm (AS s) = termS N.NoOp . norm $ s
  reify       = AS . paren . rawSession . reify

instance Norm RawSession where
  type Normalized RawSession = N.Session
  norm = termS N.NoOp . norm . rawSession
  reify = RawSession . \case
    N.Array k s      -> aTerm $ reifyArray k (reify s)
    N.IO N.Write a s -> Snd (reify a) (reify s)
    N.IO N.Read  a s -> Rcv (reify a) (reify s)
    N.TermS op e     -> dualOp op (reify e)

reifySession :: N.Session -> Term
reifySession = rawSession . reify

reifySessions :: [N.Session] -> [Term]
reifySessions = map reifySession

reifyDec :: N.Dec -> Dec
reifyDec = reify

instance Norm RSession where
  type Normalized RSession = N.RSession
  reify (N.Repl s (N.Lit (LInteger 1))) = Repl (reifySession s) One
  reify (N.Repl s t)                    = Repl (reifySession s) (Some (reify t))
  norm  (Repl s One)         = one (norm (RawSession s))
  norm  (Repl s (Some a))    = N.Repl (norm (RawSession s)) (norm a)

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
    PDot proc proc' -> norm proc `dotP` norm proc'
    PPrll procs     -> mconcat $ norm procs

instance Norm CPatt where
  type Normalized CPatt = N.CPatt
  reify (N.ChanP cd) = ChaPatt (reify cd)
  reify (N.ArrayP k ps) = k' (reify ps) where
    k' = case k of
      N.TenK -> TenPatt
      N.ParK -> ParPatt
      N.SeqK -> SeqPatt
  norm = \case
    TenPatt ps -> N.ArrayP N.TenK (norm ps)
    ParPatt ps -> N.ArrayP N.ParK (norm ps)
    SeqPatt ps -> N.ArrayP N.SeqK (norm ps)
    ChaPatt cd -> N.ChanP (norm cd)

instance Norm TopCPatt where
  type Normalized TopCPatt = N.CPatt
  reify (N.ChanP cd) = OldTopPatt [reify cd]
  reify (N.ArrayP k ps) = k' (reify ps) where
    k' = case k of
      N.TenK -> TenTopPatt
      N.ParK -> ParTopPatt
      N.SeqK -> SeqTopPatt
  norm = \case
    OldTopPatt[cd]-> N.ChanP (norm cd)
    OldTopPatt cs -> N.ArrayP N.ParK (N.ChanP . norm <$> cs)
    TenTopPatt ps -> N.ArrayP N.TenK (norm ps)
    ParTopPatt ps -> N.ArrayP N.ParK (norm ps)
    SeqTopPatt ps -> N.ArrayP N.SeqK (norm ps)

pAct :: N.Act -> Proc
pAct = PAct . reifyAct

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
    Ax        s cs    -> fwdP    ø (norm s) cs
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
    At       t pa     -> go [N.At             (norm t) (norm pa)]
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
  N.At       t ps     -> At          (reify t) (reify ps)

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
  | op `elem` ["-","+","*","/","%","-D","+D","*D","/D","++S"]
  = N.Def (Name ("_" ++ op ++ "_")) [norm e0, normRawApp es]
normRawApp (Var (Name "Fwd") : es)
  | [Lit (LInteger n), e] <- es = N.tSession $ fwd (fromInteger n) (norm (AS e))
  | otherwise = error "invalid usage of Fwd"
normRawApp (Var (Name "Log") : es)
  | [e] <- es = N.tSession $ log (norm (AS e))
  | otherwise = error "invalid usage of Log"
normRawApp (Var x : es) = N.Def x (norm es)
normRawApp [] = error "normRawApp: IMPOSSIBLE"
normRawApp _ = error "normRawApp: unexpected application"

reifyRawApp :: N.Term -> [ATerm]
reifyRawApp e0 =
  case reify e0 of
    Paren (RawApp e1 es) -> e1 : es
    e0'                  -> [e0']

instance Norm DTerm where
  type Normalized DTerm = N.VarDec

  reify (Arg x e0)
    | x == anonName, N.Def d es <- e0 = DTTyp d (reify es)
    | otherwise                       = DTBnd x (reify e0)

  norm (DTTyp d es) = anonArg (N.Def d (norm es))
  norm (DTBnd x e)  = Arg x (norm e)

reifyArray :: N.TraverseKind -> [RSession] -> ATerm
reifyArray N.ParK = Par
reifyArray N.SeqK = Seq
reifyArray N.TenK = Ten

instance Norm ATerm where
  type Normalized ATerm = N.Term

  reify = \case
    N.Def x []         -> Var x
    N.Lit l            -> Lit l
    N.Con n            -> Con (reify n)
    N.TTyp             -> TTyp
    N.TProto ss        -> TProto (reify ss)
    N.TSession
        (N.Array k ss) -> reifyArray k (reify ss)
    e                  -> paren (reify e)

  norm (Var x)          = N.Def x []
  norm (Lit l)          = N.Lit l
  norm (Con n)          = N.Con (norm n)
  norm TTyp             = N.TTyp
  norm (TProto ss)      = N.TProto (norm ss)
  norm End              = N.TSession endS
  norm (Par s)          = N.TSession $ N.Array N.ParK (norm s)
  norm (Ten s)          = N.TSession $ N.Array N.TenK (norm s)
  norm (Seq s)          = N.TSession $ N.Array N.SeqK (norm s)
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
    N.TSession s       -> reifySession s

  norm (RawApp e es)    = normRawApp (e:es)
  norm (Case t brs)     = N.Case (norm t) (sort (norm brs))
  norm (TProc cs p)     = N.Proc (norm cs) (norm p)
  norm (Lam  xs xss t)  = normVarDec N.Lam  (xs:xss) (norm t)
  norm (TFun xs xss t)  = normVarDec N.TFun (xs:xss) (norm t)
  norm (TSig xs xss t)  = normVarDec N.TSig (xs:xss) (norm t)
  norm (Snd a s)        = N.TSession $ N.IO N.Write (norm a) (norm s)
  norm (Rcv a s)        = N.TSession $ N.IO N.Read  (norm a) (norm s)
  norm (Loli s t)       = N.TSession $ norm (RawSession s) `loli` norm (RawSession t)
  norm (Dual s)         = dual (norm s)

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
  norm  ( DAsr a)       = N.Assert (norm a)

  reify (N.Sig _ Nothing   Nothing)   = error "IMPOSSIBLE Norm Dec/reify: no def nor sig"
  reify (N.Sig d (Just ty) Nothing)   = DSig d (reify ty)
  reify (N.Sig d ty        (Just tm)) = DDef d (reify ty) (reify tm)
  reify (N.Dat d cs)                  = DDat d (reify cs)
  reify (N.Assert a)                  = DAsr (reify a)

instance Norm Assertion where
  type Normalized Assertion = N.Assertion
  norm  ( AEq t1 t2 ty) = N.Equal (norm t1) (norm t2) (norm ty)
  reify (N.Equal t1 t2 ty)            = AEq (reify t1) (reify t2) (reify ty)

-- -}
