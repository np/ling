{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
module Ling.Compile.C where

{-
  programs have parameters
  the meaning is that no synch is expected
  namely if the protocol can "recv" an int on chan c, then
  it means we can read this location, similarily for send.

  TODO, so far only a naive approach is selected

  Single read parameter:

    Short type (less or equal than a word):

      void foo(const int c) { const int x0 = c; }

    Large type:

      void foo((const (const large_type) *) c) { const large_type x0 = *c; }

    Another approach would be to avoid the copy of arguments when receiving.

  Single write parameter:

    void foo(const (int *) c) { *c = 42; }

  Read then write parameter:

    void foo(const (int *) c) { const int x = *c; *c = 42; }

  example:

  test1 (c : ?int) (d : !int) (e : {!int, ?int}) (f : [!int, !int]) =
    recv c x (e(e0,e1) ...) ...
-}

import           Prelude         hiding (log)

import qualified Data.Map        as Map
import           Ling.Defs       (pushDefs)
import           Ling.Fwd        (fwdProc')
import           Ling.Norm       hiding (mkCase)
import           Ling.Prelude    hiding (q)
import           Ling.Print
import           Ling.Proc       (_Pref)
import           Ling.Reduce     (reduceTerm, reduce_)
--import           Ling.Rename     (hDec)
import           Ling.Scoped     (Scoped(Scoped))
import           Ling.Session
-- import           Ling.Subst      (unScoped)
import qualified MiniC.Abs       as C
import qualified MiniC.Print     as C

type ATyp = (C.Typ, [C.Arr])
type AQTyp = (C.QTyp, [C.Arr])

voidQ :: C.QTyp
voidQ = C.QTyp C.NoQual C.TVoid

tPtr :: Endom ATyp
tPtr = _1 %~ C.TPtr

tVoidPtr :: ATyp
tVoidPtr = (C.TPtr C.TVoid, [])

tArr :: ATyp -> C.Exp -> ATyp
tArr (ty, arrs) e = (ty, arrs ++ [C.AArr e])

tInt :: ATyp
tInt = (C.TInt, [])

tDouble :: ATyp
tDouble = (C.TDouble, [])

-- unused
eFld :: C.Exp -> C.Ident -> C.Exp
eFld (C.UOp C.UPtr l) = C.EArw l
eFld               l  = C.EFld l

lFld :: C.LVal -> C.Ident -> C.LVal
lFld (C.LPtr e) = C.LArw e
lFld         e  = C.LFld e

isEmptyTyp :: C.Typ -> Bool
isEmptyTyp C.TVoid     = True
isEmptyTyp (C.TStr []) = True
isEmptyTyp _           = False

isEmptyQTyp :: C.QTyp -> Bool
isEmptyQTyp (C.QTyp _ t) = isEmptyTyp t

isEmptyAQTyp :: AQTyp -> Bool
isEmptyAQTyp = isEmptyQTyp . fst

dDec :: AQTyp -> C.Ident -> C.Dec
dDec (qt, arrs) x = C.Dec qt x arrs

sDec :: AQTyp -> C.Ident -> C.Init -> [C.Stm]
sDec aqtyp cid ini
  | isEmptyAQTyp aqtyp = []
  | otherwise          = [C.SDec (dDec aqtyp cid) ini]

dSig :: C.Dec -> [C.Dec] -> C.Def
dSig d [] = C.DDec d
dSig d ds = C.DSig d ds

type EVar = Name

data Env =
  Env { _locs  :: Map Channel C.LVal
      , _evars :: Map EVar C.Ident
      , _edefs :: Defs
      , _types :: Set Name
      , _farr  :: Bool
      }
  deriving (Show)

$(makeLenses ''Env)

basicTypes :: Map Name C.Typ
basicTypes = l2m [ (Name n, t) | (n,t) <-
  [("Int", C.TInt)
  ,("Double", C.TDouble)
  ,("String", C.TPtr C.TChar)
  ,("Char", C.TChar)] ]

primTypes :: Set Name
primTypes = l2s (Name "Vec" : keys basicTypes)

emptyEnv :: Env
emptyEnv = Env ø ø ø primTypes True

addChans :: [(Name, C.LVal)] -> Endom Env
addChans xys env = env & locs %~ Map.union (l2m xys)

rmChan :: Channel -> Endom Env
rmChan c env = env & locs .\\ c

rmChans :: [Channel] -> Endom Env
rmChans = composeMapOf each rmChan

renChan :: Channel -> Channel -> Endom Env
renChan c c' env = env & locs . at c' .~ (env ^. locs . at c)
                       & rmChan c

addEVar :: Name -> C.Ident -> Endom Env
addEVar x y env
  | env ^. evars . hasKey x = error $ "addEVar/IMPOSSIBLE: " ++ show x ++ " is already bound"
  | otherwise               = env & evars . at x ?~ y

(!) :: Env -> Name -> C.LVal
(!) = lookupEnv _Name locs

transCon :: Name -> C.Ident
transCon (Name x) = C.Ident ("con_" ++ x)

transName :: Name -> C.Ident
transName (Name x) = C.Ident (concatMap f x ++ "_lin") where
  f '#'  = "__"
  f '\'' = "__"
  f '+'  = "_plus_"
  f '*'  = "_times_"
  f '/'  = "_div_"
  f '-'  = "_sub_"
  f  c   = [c]

transOp :: EVar -> Maybe (Op2 C.Exp)
transOp (Name v) = (\f x y -> C.EParen (f x y)) <$> case v of
  "_+_"  -> Just C.Add
  "_+D_" -> Just C.Add
  "_*_"  -> Just C.Mul
  "_*D_" -> Just C.Mul
  "_/_"  -> Just C.Div
  "_/D_" -> Just C.Div
  "_%_"  -> Just C.Mod
  "_%D_" -> Just C.Mod
  "_-_"  -> Just C.Sub
  "_-D_" -> Just C.Sub
  _      -> Nothing

transEVar :: Env -> EVar -> C.Ident
transEVar env y = env ^. evars . at y ?| transName y

mkCase :: C.Ident -> [C.Stm] -> C.Branch
mkCase = C.Case . C.EVar

switch :: C.Exp -> [(C.Ident,[C.Stm])] -> C.Stm
switch e brs = C.SSwi e (uncurry mkCase <$> brs)

isEVar :: C.Exp -> Bool
isEVar C.EVar{} = True
isEVar _        = False

switchE :: C.Exp -> [(C.Ident,C.Exp)] -> C.Exp
switchE e brs
  -- If there is less than 3 branches then only comparison is done,
  -- if `e` is a variable then it is cheap to compare it multiple times
  | length brs < 3 || isEVar e =
      case brs of
        [] -> e -- dynamically impossible because of `e`, so just return `e`
        [(_i0,e0)]  -> e0 -- x must be equal to _i0, to go directly to e0
        (i0,e0):ies -> C.Cond (C.Eq e (C.EVar i0)) e0 (switchE e ies)
  | otherwise =
  -- This could be replaced by a warning instead
      transErrC "switchE" e

transLiteral :: Literal -> C.Literal
transLiteral l = case l of
  LInteger n -> C.LInteger n
  LDouble  d -> C.LDouble  d
  LString  s -> C.LString  s
  LChar    c -> C.LChar    c

transTerm :: Env -> Term -> C.Exp
transTerm env t0 =
  let t1 = reduceTerm' env t0 in case t1 of
  Def f es0
   | env ^. types . contains f -> dummyTyp
   | otherwise ->
     case transTerm env <$> es0 of
       []                             -> C.EVar (transEVar env f)
       [e0,e1] | Just d <- transOp f  -> d e0 e1
       es                             -> C.EApp (C.EVar (transName f)) es
  Let{}          -> error "IMPOSSIBLE: Let after reduce"
  Lit l          -> C.ELit (transLiteral l)
  Lam{}          -> transErr "transTerm/Lam" t1
  Con n          -> C.EVar (transCon n)
  Case t brs     -> switchE (transTerm env t)
                            (bimap transCon (transTerm env) <$> brs)
  Proc{}         -> transErr "transTerm/Proc" t1
  TFun{}         -> dummyTyp
  TSig{}         -> dummyTyp
  TProto{}       -> dummyTyp
  TTyp           -> dummyTyp
  TSession{}     -> dummyTyp -- so far one cannot match on sessions

-- Types are erased to 0
dummyTyp :: C.Exp
dummyTyp = C.ELit (C.LInteger 0)

transProc :: Env -> Proc -> [C.Stm]
transProc env = \case
  proc0 `Dot` proc1
    | Just pref <- proc0 ^? _Pref -> transPref env pref proc1
    | otherwise                   -> transProc env proc0 ++ transProc env proc1
  Act act -> transAct env act ^. _2
  Procs (Prll procs) ->
    case procs of
      [] -> []
      [p] -> transErr "transProc/Procs/[_] not a normal form" p
      _   -> transErr "transProc/Procs: parallel processes should be in sequence" (Prll procs)
  NewSlice cs r xi proc0 ->
    [stdFor (transName xi) (transRFactor env r) $
       transProc env' proc0]
    where
      i = transName xi
      sliceIf c l | c `elem` cs = C.LArr l (C.EVar i)
                  | otherwise   = l
      env' = env & locs . imapped %@~ sliceIf
                  & addEVar xi i

transLVal :: C.LVal -> C.Exp
transLVal (C.LVar x)   = C.EVar x
transLVal (C.LFld l f) = eFld   (transLVal l) f
transLVal (C.LArw l f) = C.EArw (transLVal l) f
transLVal (C.LArr l i) = C.EArr (transLVal l) i
transLVal (C.LPtr l)   = ePtr   (transLVal l)

ePtr :: Endom C.Exp
ePtr = C.UOp C.UPtr

transErr :: Print a => String -> a -> b
transErr msg v = error $ msg ++ "\n" ++ pretty v

transErrC :: C.Print a => String -> a -> b
transErrC msg v = error $ msg ++ "\n" ++ C.render (C.prt 0 v)

transNewPatt :: Env -> NewPatt -> (Env, [C.Stm])
transNewPatt env = \case
  NewChans _ cds -> (env', sDec typ cid C.NoInit)
    where
      cs   = cds ^.. each . cdChan
      cOSs = cds ^.. each . cdSession
      s    = log $ extractSession cOSs
      cid  = transName (cs ^?! _head)
      l    = C.LVar cid
      typ  = transRSession env s
      env' = addChans [(c,l) | c <- cs] env

  NewChan c mty -> (env', sDec typ cid C.NoInit)
    where
      cid  = transName c
      l    = C.LVar cid
      typ  = transMaybeCTyp env C.NoQual mty
      env' = addChans [(c,l)] env

-- Implement the effect of an action over:
-- * an environment
-- * a list of statements
transAct :: Env -> Act -> (Env, [C.Stm])
transAct env act =
  case act of
    Nu _ann newpatt -> transNewPatt env newpatt
      -- Issue #24: the annotation should be used to decide
      -- operational choices on channel allocation.
    Split _ c ds ->
      (transSplit c ds env, [])
    Send c expr ->
      (env, [C.SPut (env ! c) (transTerm env expr)])
    Recv c (Arg x typ) ->
      (addEVar x (transName x) env, sDec ctyp y cinit)
      where
        ctyp  = transMaybeCTyp (env & farr .~ False) C.QConst typ
        y     = transName x
        cinit = C.SoInit (transLVal (env!c))
    Ax s cs ->
      case fwdProc' (reduceSession env) s cs of
        Act (Ax{}) -> transErr "transAct/Ax" act
        proc0 -> (rmChans cs env, transProc env proc0)
    At t p ->
      case p of
        ChanP (ChanDec c _ _) ->
          case reduceTerm' env t of
            Proc cs proc0 ->
              case cs of
                [ChanDec c' _ _] ->
                  let env1 = renChan c c' env in
                  (rmChan c env, transMkProc env1 cs proc0 ^. _2)
                _ -> transErr "transAct/At/Non single proc" act
            _ -> transErr "transAct/At/Non Proc" act
        _ -> transErr "transAct/At/Non ChanP" act
    LetA defs ->
      (env & edefs <>~ defs, [])

-- The actions in this prefix are in parallel and thus can be reordered
transPref :: Env -> Pref -> Proc -> [C.Stm]
transPref env (Prll acts0) proc1 =
  case acts0 of
    [] -> transProc env proc1
    act:acts ->
      let (env', actStm) = transAct env act in
      actStm ++ transPref env' (Prll acts) proc1

{- stdFor i t body ~~~> for (int i = 0; i < t; i = i + 1) { body } -}
stdFor :: C.Ident -> C.Exp -> [C.Stm] -> C.Stm
stdFor i t =
  C.SFor (C.SDec (C.Dec (C.QTyp C.NoQual C.TInt) i []) (C.SoInit (C.ELit (C.LInteger 0))))
         (C.Lt (C.EVar i) t)
         (C.SPut (C.LVar i) (C.Add (C.EVar i) (C.ELit (C.LInteger 1))))

{- Special case:
   {S}/[S] has the same implementation as S.
   See tupQ -}
transSplit :: Name -> [ChanDec] -> Endom Env
transSplit c dOSs env = rmChan c $ addChans news env
  where
    lval = env ! c
    ds   = _cdChan <$> dOSs
    news =
      case ds of
        [d] -> [ (d, lval) ]
        _   -> [ (d, lval')
               | (d,n) <- zip ds [0..]
               , let lval' = lFld lval (fldI n)
               ]

fldI :: Int -> C.Ident
fldI n = C.Ident ("f" ++ show n)

uniI :: Int -> C.Ident
uniI n = C.Ident ("u" ++ show n)

unionT :: [ATyp] -> ATyp
unionT ts
  | Just t <- theUniq ts = t
  | otherwise            = (u, [])
      where u = C.TUni [ C.FFld t (uniI i) arrs | (i,(t,arrs)) <- zip [0..] ts ]

rwQual :: RW -> C.Qual
rwQual Read  = C.QConst
rwQual Write = C.NoQual

unionQual :: Op2 C.Qual
unionQual C.QConst C.QConst = C.QConst
unionQual _        _        = C.NoQual

unionQuals :: [C.Qual] -> C.Qual
unionQuals = foldr unionQual C.QConst

unionQ :: [AQTyp] -> AQTyp
unionQ ts = (_1 %~ C.QTyp (unionQuals [ q     | (C.QTyp q _, _) <- ts ]))
            (unionT     [ (t,a) | (C.QTyp _ t, a) <- ts, not (isEmptyTyp t) ])

{- See transSplit about the special case -}
tupQ :: [AQTyp] -> AQTyp
tupQ [t] = t
tupQ ts = (C.QTyp (unionQuals [ q | (C.QTyp q _, _) <- ts ])
                  (C.TStr     [ C.FFld t (fldI i) arrs | (i,(C.QTyp _ t,arrs)) <- zip [0..] ts ])
          ,[])

unsupportedTyp :: Typ -> ATyp
unsupportedTyp ty = trace ("[WARNING] Unsupported type " ++ pretty ty) tVoidPtr

transTyp :: Env -> Typ -> ATyp
transTyp env ty0 =
  let ty1 = reduceTerm' env ty0 in case ty1 of
  Def x es
    | null es, Just t <- Map.lookup x basicTypes -> (t, [])
    | otherwise ->
    case (unName # x, es) of
      ("Vec", [a,e])
        | env ^. farr, Just i <- reduceTerm' env e ^? _Lit . _LInteger ->
           -- Here we could use transTerm if we could still fallback on a
           -- pointer type.
            tArr (transTyp env a) (C.ELit (C.LInteger i))
        | otherwise -> tPtr (transTyp env a)
      _ -> unsupportedTyp ty0
  Let{}      -> error "IMPOSSIBLE: Let after reduce"
  TTyp{}     -> tInt -- <- types are erased to 0
  Case{}     -> unsupportedTyp ty0
  TProto{}   -> unsupportedTyp ty0
  TFun{}     -> unsupportedTyp ty0
  TSig{}     -> unsupportedTyp ty0
  TSession{} -> unsupportedTyp ty0
  Lam{}      -> transErr "transTyp: Not a type: Lam" ty0
  Lit{}      -> transErr "transTyp: Not a type: Lit" ty0
  Con{}      -> transErr "transTyp: Not a type: Con" ty0
  Proc{}     -> transErr "transTyp: Not a type: Proc" ty0

transCTyp :: Env -> C.Qual -> Typ -> AQTyp
transCTyp env qual = (_1 %~ C.QTyp qual) . transTyp env

transMaybeCTyp :: Env -> C.Qual -> Maybe Typ -> AQTyp
transMaybeCTyp env qual = \case
  Nothing -> error "transMabyeCTyp: Missing type annotation"
  Just ty -> transCTyp env qual ty

{-
mapQTyp :: Endom C.Typ -> Endom C.QTyp
mapQTyp f (C.QTyp  q t) = C.QTyp q (f t)
-}

-- LENSME
mapAQTyp :: Endom ATyp -> Endom AQTyp
mapAQTyp f (C.QTyp  q t , arrs) = (C.QTyp q t', arrs')
  where (t', arrs') = f (t, arrs)

transSession :: Env -> Session -> AQTyp
transSession env x = case x of
  IO rw (Arg n ty) s
    | n == anonName -> unionQ [transMaybeCTyp env (rwQual rw) ty, transSession env s]
    | otherwise     -> transErr "Cannot compile a dependent session (yet): " x
  Array _ ss -> tupQ (transSessions env ss)
  TermS p t ->
    case reduceTerm' env t of
      TSession s -> transSession env (sessionOp p s)
      ty         -> unsupportedTyp ty & _1 %~ C.QTyp C.NoQual

transRFactor :: Env -> RFactor -> C.Exp
transRFactor env (RFactor t) = transTerm env t

transRSession :: Env -> RSession -> AQTyp
transRSession env (s `Repl` r)
  | litR1 `is` r = transSession env s
  | otherwise    = mapAQTyp (\t -> tArr t (transRFactor env r)) (transSession env s)

transSessions :: Env -> Sessions -> [AQTyp]
transSessions = map . transRSession

isPtrTyp :: C.Typ -> Bool
isPtrTyp (C.TPtr _) = True
isPtrTyp _          = False

isPtrQTyp :: AQTyp -> Bool
isPtrQTyp (C.QTyp _ t, []) = isPtrTyp t
isPtrQTyp _                = True

-- Turns a type into a pointer unless it is one already.
mkPtrTyp :: AQTyp -> (AQTyp, Endom C.LVal)
mkPtrTyp ctyp
  | isPtrQTyp ctyp = (ctyp, id)
  | otherwise      = (mapAQTyp tPtr ctyp, C.LPtr)

transChanDec :: Env -> ChanDec -> (C.Dec , (Channel, C.LVal))
transChanDec env (ChanDec c _ (Just session)) =
    (dDec ctyp d, (c, trlval (C.LVar d)))
  where
    d              = transName c
    (ctyp, trlval) = mkPtrTyp (transRSession env session)
transChanDec _   (ChanDec c _ Nothing)
  = transErr "transChanDec: TODO No Session for channel:" c

transMkProc :: Env -> [ChanDec] -> Proc -> ([C.Dec], [C.Stm])
transMkProc env0 cs proc0 = (fst <$> news, transProc env proc0)
  where
    news = transChanDec env0 <$> cs
    env  = addChans (snd <$> news) env0

transSig :: Env -> Name -> Maybe Typ -> Maybe Term -> [C.Def]
transSig env0 f _ty0 (Just t) =
  case reduceTerm' env0 t of
    Proc cs proc0 ->
      [uncurry (C.DDef (C.Dec voidQ (transName f) []))
               (transMkProc env0 cs proc0)]
    _ -> trace ("[WARNING] Skipping compilation of unsupported definition " ++ pretty f) []
-- Of course this does not properly handle dependent types
transSig env0 f (Just ty0) Nothing = go [] (reduceTerm' env0 ty0)
  where
    go args = \case
      TFun (Arg n ms) t ->
        go (dDec (transMaybeCTyp env0 C.QConst ms) (transName n) : args)
           (reduceTerm' (addEVar n (transName n) env0) t)
      t1 ->
        [dSig (dDec (transCTyp env0 C.NoQual t1) (transName f)) (reverse args)]
transSig _ _ Nothing Nothing = error "IMPOSSIBLE transSig no sig nor def"

transDec :: Env -> Dec -> (Env, [C.Def])
transDec env dec = case {-hDec-} dec of
  Sig d ty tm -> (env & edefs . at d .~ (Ann ty <$> tm), transSig env d ty tm)
  Dat _d _cs ->
    (env, []) -- TODO typedef ? => [C.TEnum (C.EEnm . transCon <$> cs)]
  Assert _a ->
    (env, []) -- could be an assert.. but why?

transProgram :: Program -> C.Prg
transProgram (Program decs) =
  C.PPrg (mapAccumL transDec emptyEnv decs ^.. _2 . each . each)

reduceTerm' :: Env -> Endom Term
reduceTerm' env = pushDefs . reduceTerm . Scoped (env ^. edefs) ø

reduceSession :: Env -> Endom Session
reduceSession env = pushDefs . reduce_ tSession . Scoped (env ^. edefs) ø
-- -}
-- -}
-- -}
-- -}
