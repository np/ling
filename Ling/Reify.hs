{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Ling.Reify where

import qualified Ling.Norm    as N
import           Ling.Prelude
import           Ling.Proc
import           Ling.Raw
import           Ling.Session
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
  norm = map norm

instance Norm CSession where
  type Normalized CSession = N.Session
  reify s
    | s == endS = Done
    | otherwise = Cont . rawSession $ reify s
  norm Done = endS
  norm (Cont s) = norm (RawSession s)

instance Norm ASession where
  type Normalized ASession = N.Session
  norm (AS s) = termS N.NoOp . norm $ s
  reify = AS . paren . rawSession . reify

instance Norm RawSession where
  type Normalized RawSession = N.Session
  norm = termS N.NoOp . norm . rawSession
  reify = RawSession . \case
            N.Array k s      -> aTerm $ reifyArray k (reify s)
            N.IO N.Write a s -> Snd (reify a) (reify s)
            N.IO N.Read a s  -> Rcv (reify a) (reify s)
            N.TermS o e      -> dualOp o (reify e)

reifySession :: N.Session -> Term
reifySession = rawSession . reify

reifySessions :: [N.Session] -> [Term]
reifySessions = map reifySession

reifyDec :: N.Dec -> Dec
reifyDec = reify

instance Norm OptRepl where
  type Normalized OptRepl = N.RFactor
  reify (N.isLitR -> Just 1) = One
  reify (N.RFactor t)        = Some (reify t)
  norm  One                  = ø
  norm (Some t)              = N.RFactor (norm t)

instance Norm RSession where
  type Normalized RSession = N.RSession
  reify (N.Repl s r) = Repl (reifySession s) (reify r)
  norm  (Repl s r)   = N.Repl (norm (RawSession s)) (norm r)

reifyRSession :: N.RSession -> RSession
reifyRSession = reify

reifyRSessions :: [N.RSession] -> [RSession]
reifyRSessions = reify

instance Norm Proc where
  type Normalized Proc        = N.Proc
  reify (N.Dot pref procs)    = reifyPref pref (mkProcs $ reify procs)
  norm = \case
    PAct act         -> normAct act
    PNxt proc0 proc1 -> norm proc0 `nxtP` norm proc1
    PDot proc0 proc1 -> norm proc0 `dotP` norm proc1
    PPrll procs      -> mconcat $ norm procs

kCPatt :: N.TraverseKind -> [CPatt] -> CPatt
kCPatt = \case
  N.TenK -> TenPatt
  N.ParK -> ParPatt
  N.SeqK -> SeqPatt

kTopPatt :: N.TraverseKind -> [CPatt] -> TopCPatt
kTopPatt = \case
  N.TenK -> TenTopPatt
  N.ParK -> ParTopPatt
  N.SeqK -> SeqTopPatt

instance Norm CPatt where
  type Normalized CPatt = N.CPatt
  reify (N.ChanP cd) = ChaPatt (reify cd)
  reify (N.ArrayP k ps) = kCPatt k (reify ps)
  norm = \case
    TenPatt ps -> N.ArrayP N.TenK (norm ps)
    ParPatt ps -> N.ArrayP N.ParK (norm ps)
    SeqPatt ps -> N.ArrayP N.SeqK (norm ps)
    ChaPatt cd -> N.ChanP (norm cd)

instance Norm TopCPatt where
  type Normalized TopCPatt = N.CPatt
  reify (N.ChanP cd) = OldTopPatt [reify cd]
  reify (N.ArrayP k ps) = kTopPatt k (reify ps)
  norm = \case
    OldTopPatt [cd] -> N.ChanP (norm cd)
    OldTopPatt cs   -> N.ArrayP N.ParK (N.ChanP . norm <$> cs)
    TenTopPatt ps   -> N.ArrayP N.TenK (norm ps)
    ParTopPatt ps   -> N.ArrayP N.ParK (norm ps)
    SeqTopPatt ps   -> N.ArrayP N.SeqK (norm ps)

pAct :: N.Act -> Proc
pAct = PAct . reifyAct

reifyPref :: N.Pref -> Endom Proc
reifyPref = \case
  [] -> id
  [act]
    | N.actNeedsDot act -> pDot (pAct act)
    | otherwise -> pNxt (pAct act)
  acts -> pDot (PPrll (pAct <$> acts))

noSoSession :: ChanDec -> Name
noSoSession (CD x NoSession) = x
noSoSession (CD (Name x) SoSession{}) = error $
  "unexpected session annotation for channel " ++ x

normAct :: Act -> N.Proc
normAct = \case
    -- These two clauses expand the forwarders
    Ax        s cs    -> fwdP    ø (norm s) (noSoSession <$> cs)
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
    NewSlice cs t x   -> go [N.NewSlice (noSoSession <$> cs) (norm (Some t)) x]
    At       t pa     -> go [N.At                            (norm t) (norm pa)]
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
  N.NewSlice cs t x   -> NewSlice ((`CD` NoSession) <$> cs) (reify (t ^. N.rterm)) x
  N.Ax       s cs     -> Ax          (reify s) ((`CD` NoSession) <$> cs)
  N.At       t ps     -> At          (reify t) (reify ps)

-- isInfix xs = match "_[^_]*_" xs
isInfix :: Name -> Maybe Name
isInfix (Name ('_':xs@(_:_:_)))
  | last xs == '_' && '_' `notElem` s =
      Just (Name s)
  where
    s = init xs
isInfix _ = Nothing

-- Really naive rawApp parsing
-- Next step is to carry an environment with
-- the operators and their fixity.
-- TODO:
--   * this only supports naive right-infix
--   * this currently fails to parse: `f x + y`
normRawApp :: [ATerm] -> N.Term
normRawApp [e] = norm e
normRawApp (e0:Var (Name d):es)
  | d `elem` ["-", "+", "*", "/", "%", "-D", "+D", "*D", "/D", "++S"] =
      N.Def (Name ("_" ++ d ++ "_")) [norm e0, normRawApp es]
normRawApp (Var (Name "Fwd"):es)
  | [Lit (LInteger n), e] <- es = N.tSession $ fwd (fromInteger n) (norm (AS e))
  | otherwise = error "invalid usage of Fwd"
normRawApp (Var (Name "Log"):es)
  | [e] <- es = N.tSession $ log (norm (AS e))
  | otherwise = error "invalid usage of Log"
normRawApp (Var x:es) = N.Def x (norm es)
normRawApp [] = error "normRawApp: IMPOSSIBLE"
normRawApp _ = error "normRawApp: unexpected application"

reifyRawApp :: N.Term -> [ATerm]
reifyRawApp e0 =
  case reify e0 of
    Paren (RawApp e1 es) NoSig -> e1 : es
    e0'                        -> [e0']

instance Norm DTerm where
  type Normalized DTerm = N.VarDec
  reify (Arg x e0)
    | x == anonName,
      N.Def d es <- e0
    = DTTyp d (reify es)
    | otherwise = DTBnd x (reify e0)
  norm (DTTyp d es) = anonArg (N.Def d (norm es))
  norm (DTBnd x e) = Arg x (norm e)

reifyArray :: N.TraverseKind -> [RSession] -> ATerm
reifyArray N.ParK = Par
reifyArray N.SeqK = Seq
reifyArray N.TenK = Ten

instance Norm ATerm where
  type Normalized ATerm = N.Term
  reify = \case
    N.Def x []                -> Var x
    N.Lit l                   -> Lit l
    N.Con n                   -> Con (reify n)
    N.TTyp                    -> TTyp
    N.TProto ss               -> TProto (reify ss)
    N.TSession (N.Array k ss) -> reifyArray k (reify ss)
    e                         -> paren (reify e)
  norm = \case
    Var x      -> N.Def x []
    Lit l      -> N.Lit l
    Con n      -> N.Con (norm n)
    TTyp       -> N.TTyp
    TProto ss  -> N.TProto (norm ss)
    End        -> N.TSession endS
    Par s      -> N.TSession $ N.Array N.ParK (norm s)
    Ten s      -> N.TSession $ N.Array N.TenK (norm s)
    Seq s      -> N.TSession $ N.Array N.SeqK (norm s)
    Paren t os -> N.optSig (norm t) (norm os)

mkVsD :: ATerm -> VarsDec
mkVsD = \case
  Paren (RawApp (Var x) as) (SoSig s)
    | let xs = [y | Var y <- as],
      length xs == length as
    -> VsD x xs s
  e ->
    VsD anonName [] (aTerm e)

mkVsDs :: Term -> [VarsDec]
mkVsDs = \case
  RawApp a as -> mkVsD <$> (a : as)
  e           -> error $ "Expecting bindings (x... : T)... not: " ++ show e

reifyDef :: Name -> [N.Term] -> Term
reifyDef x es
  | [e1, e2] <- es,
    Just d <- isInfix x
  = RawApp (reify e1) (Var d : reifyRawApp e2)
  | otherwise = RawApp (Var x) (reify es)

instance Norm Term where
  type Normalized Term = N.Term
  reify = \case
    N.Def x es         -> reifyDef x es
    N.Lit l            -> RawApp (Lit l) []
    N.Con n            -> RawApp (Con (reify n)) []
    N.TTyp             -> RawApp TTyp []
    N.TProto ss        -> RawApp (TProto (reify ss)) []
    N.Proc cs p        -> TProc (reify cs) (reify p)
    N.Lam (Arg a t) s  -> Lam (VsD a [] (reify t)) [] (reify s)
    N.TFun (Arg a t) s -> TFun (RawApp (Paren (RawApp (Var a) []) (SoSig (reify t))) []) (reify s)
    N.TSig (Arg a t) s -> TSig (RawApp (Paren (RawApp (Var a) []) (SoSig (reify t))) []) (reify s)
    N.Case t brs       -> Case (reify t) (reify brs)
    N.TSession s       -> reifySession s
  norm = \case
    RawApp e es  -> normRawApp (e : es)
    Case t brs   -> N.Case (norm t) (sort (norm brs))
    TProc cs p   -> N.Proc (norm cs) (norm p)
    Lam xs xss t -> normVarsDecs N.Lam (xs : xss) (norm t)
    TFun u t     -> normVarsDecs N.TFun (mkVsDs u) (norm t)
    TSig u t     -> normVarsDecs N.TSig (mkVsDs u) (norm t)
    Snd a s      -> N.TSession $ N.IO N.Write (norm a) (norm s)
    Rcv a s      -> N.TSession $ N.IO N.Read (norm a) (norm s)
    Loli s t     -> N.TSession $ norm (RawSession s) `loli` norm (RawSession t)
    Dual s       -> dual (norm s)

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

normVarsDecs :: (Arg N.Term -> N.Term -> N.Term) -> [VarsDec] -> N.Term -> N.Term
normVarsDecs f vsds z =
  foldr f z [Arg y (norm s) | VsD x xs s <- vsds
                            , y <- x : xs]

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

  norm = \case
    DSig d ty    -> N.Sig d (Just $ norm ty) Nothing
    DDef d ty tm -> N.Sig d (norm ty) (Just $ norm tm)
    DDat d cs    -> N.Dat d (norm cs)
    DAsr a       -> N.Assert (norm a)
  reify = \case
    N.Sig _ Nothing   Nothing -> error "IMPOSSIBLE Norm Dec/reify: no def nor sig"
    N.Sig d (Just ty) Nothing -> DSig d (reify ty)
    N.Sig d ty (Just tm)      -> DDef d (reify ty) (reify tm)
    N.Dat d cs                -> DDat d (reify cs)
    N.Assert a                -> DAsr (reify a)

instance Norm Assertion where
  type Normalized Assertion = N.Assertion
  norm  (AEq t1 t2 ty)      = N.Equal (norm t1) (norm t2) (norm ty)
  reify (N.Equal t1 t2 ty)  = AEq (reify t1) (reify t2) (reify ty)

-- -}
