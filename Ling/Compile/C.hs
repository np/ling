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
import           Ling.Fwd        (fwdProc')
import           Ling.Norm       hiding (mkCase)
import           Ling.Prelude    hiding (q)
import           Ling.Print
import           Ling.Proc       (_Pref, _ArrayCs)
import           Ling.Reduce     (reduce, reduced)
--import           Ling.Rename     (hDec)
import           Ling.Session
import           Ling.Scoped     (Scoped(Scoped), ldefs, scoped)
import           Ling.Subst      (reduceS)
import qualified MiniC.Abs       as C
import qualified MiniC.Print     as C

type ATyp = (C.Typ, [C.Arr])
type AQTyp = (C.QTyp, [C.Arr])

qQual :: Lens' C.QTyp C.Qual
qQual f (C.QTyp q t) = (`C.QTyp` t) <$> f q

qTyp :: Lens' C.QTyp C.Typ
qTyp f (C.QTyp q t) = (C.QTyp q) <$> f t

aqATyp :: Lens' AQTyp ATyp
aqATyp = qTyp `alongside` id

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

scope :: Getter Env (Scoped ())
scope = to $ \env -> Scoped (env ^. edefs) ø ()

addScope :: Scoped a -> Endom Env
addScope s = edefs <>~ s ^. ldefs

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
transTerm env0 tm0 =
  let
    stm1 = reduce (env0 ^. scope $> tm0) ^. reduced
    env1 = env0 & addScope stm1
    tm1  = stm1 ^. scoped
  in case tm1 of
  Def _ f es0
   | env1 ^. types . contains f -> dummyTyp
   | otherwise ->
     case transTerm env1 <$> es0 of
       []                             -> C.EVar (transEVar env1 f)
       [e0,e1] | Just d <- transOp f  -> d e0 e1
       es                             -> C.EApp (C.EVar (transName f)) es
  Let{}          -> error $ "IMPOSSIBLE: Let after reduce (" ++ ppShow tm1 ++ ")"
  Lit l          -> C.ELit (transLiteral l)
  Lam{}          -> transErr "transTerm/Lam" tm1
  Con n          -> C.EVar (transCon n)
  Case t brs     -> switchE (transTerm env1 t)
                            (bimap transCon (transTerm env1) <$> brs)
  Proc{}         -> transErr "transTerm/Proc" tm1
  TFun{}         -> dummyTyp
  TSig{}         -> dummyTyp
  TProto{}       -> dummyTyp
  TTyp           -> dummyTyp
  TSession{}     -> dummyTyp -- so far one cannot match on sessions

-- Types are erased to 0
dummyTyp :: C.Exp
dummyTyp = C.ELit (C.LInteger 0)

transProc :: Env -> Proc -> [C.Stm]
transProc env0 proc0 =
  let
    proc1 = reduce (env0 ^. scope $> proc0) ^. reduced
    env1  = env0 & addScope proc1
  in
  case proc1 ^. scoped of
    proc2 `Dot` proc3
      | Just pref <- proc2 ^? _Pref -> transPref env1 pref proc3
      | otherwise                   -> transProc env1 proc2 ++ transProc env1 proc3
    Act act -> transAct env1 act ^. _2
    LetP defs proc2 ->
      transProc (env1 & edefs <>~ defs) proc2
    Procs (Prll procs) ->
      case procs of
        [] -> []
        [p] -> transErr "transProc/Procs/[_] not a normal form" p
        _   -> transErr "transProc/Procs: parallel processes should be in sequence" (Prll procs)
    Replicate _k r xi proc2 ->
      [stdFor (transName xi) (transRFactor env1 r) $
        transProc env2 proc2]
      where
        i = transName xi
        slice l = C.LArr l (C.EVar i)
        env2 = env1 & locs . mapped %~ slice
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
    Split c pat ->
      case pat ^? _ArrayCs of
        Just (_, ds) -> (transSplit c ds env, [])
        Nothing -> error "Sequential.transAct unsupported split"
    Send c _ expr ->
      (env, [C.SPut (env ! c) (transTerm env expr)])
    Recv c (Arg x typ) ->
      (addEVar x (transName x) env, sDec ctyp y cinit)
      where
        ctyp  = transMaybeCTyp (env & farr .~ False) C.QConst typ
        y     = transName x
        cinit = C.SoInit (transLVal (env!c))
    Ax s cs ->
      -- TODO this should disappear once Ax becomes a term level primitive.
      case fwdProc' (reduceS . (env ^. scope $>)) s cs of
        Act (Ax{}) -> transErr "transAct/Ax" act
        proc0 -> (rmChans cs env, transProc env proc0)
    At{} ->
      transErr "transAct/At (should have been reduced before)" act

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
transTyp env0 ty0 =
  let
    sty1 = reduce (env0 ^. scope $> ty0) ^. reduced
    env1 = env0 & addScope sty1
    ty1  = sty1 ^. scoped
  in case ty1 of
  Def _ x es
    | null es, Just t <- Map.lookup x basicTypes -> (t, [])
    | otherwise ->
    case (unName # x, es) of
      ("Vec", [a,e])
        | env1 ^. farr, Just i <- reduce (env1 ^. scope $> e) ^? reduced . scoped . _Lit . _LInteger ->
           -- Here we could use transTerm if we could still fallback on a
           -- pointer type.
            tArr (transTyp env1 a) (C.ELit (C.LInteger i))
        | otherwise -> tPtr (transTyp env1 a)
      _ -> unsupportedTyp ty1
  Let{}      -> error $ "IMPOSSIBLE: Let after reduce (" ++ ppShow ty1 ++ ")"
  TTyp{}     -> tInt -- <- types are erased to 0
  Case{}     -> unsupportedTyp ty1
  TProto{}   -> unsupportedTyp ty1
  TFun{}     -> unsupportedTyp ty1
  TSig{}     -> unsupportedTyp ty1
  TSession{} -> unsupportedTyp ty1
  Lam{}      -> transErr "transTyp: Not a type: Lam" ty1
  Lit{}      -> transErr "transTyp: Not a type: Lit" ty1
  Con{}      -> transErr "transTyp: Not a type: Con" ty1
  Proc{}     -> transErr "transTyp: Not a type: Proc" ty1

transCTyp :: Env -> C.Qual -> Typ -> AQTyp
transCTyp env qual = (_1 %~ C.QTyp qual) . transTyp env

transMaybeCTyp :: Env -> C.Qual -> Maybe Typ -> AQTyp
transMaybeCTyp env qual = \case
  Nothing -> error "transMabyeCTyp: Missing type annotation"
  Just ty -> transCTyp env qual ty

transSession :: Env -> Session -> AQTyp
transSession env x = case x of
  IO rw (Arg n ty) s
    | n == anonName -> unionQ [transMaybeCTyp env (rwQual rw) ty, transSession env s]
    | otherwise     -> transErr "Cannot compile a dependent session (yet): " x
  Array _ ss -> tupQ (transSessions env ss)
  TermS p t ->
    let t' = reduce ((env ^. scope) $> t) ^. reduced in
    case t' ^. scoped of
      TSession s -> transSession (env & addScope t') (sessionOp p s)
      ty         -> unsupportedTyp ty & _1 %~ C.QTyp C.NoQual

transRFactor :: Env -> RFactor -> C.Exp
transRFactor env (RFactor t) = transTerm env t

transRSession :: Env -> RSession -> AQTyp
transRSession env (s `Repl` r)
  | litR1 `is` r = transSession env s
  | otherwise    = transSession env s & aqATyp %~ (`tArr` transRFactor env r)

transSessions :: Env -> Sessions -> [AQTyp]
transSessions env = map (transRSession env) . view _Sessions

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
  | otherwise      = (ctyp & aqATyp %~ tPtr, C.LPtr)

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

-- Of course this does not properly handle dependent types
transSig :: Env -> Name -> Maybe Typ -> Term -> [C.Def]
transSig env0 f mty0 tm
  | Def Undefined f' [] <- tm, f == f' =
    case mty0 of
      Nothing -> error "IMPOSSIBLE transSig missing type signature"
      Just ty0 ->
        let
          go env1 ty1 args =
            let
              sty2 = reduce (env1 ^. scope $> ty1) ^. reduced
              env2 = env1 & addScope sty2
            in
            case sty2 ^. scoped of
              TFun (Arg n ms) t ->
                go (addEVar n (transName n) env2) t
                   (dDec (transMaybeCTyp env2 C.QConst ms) (transName n) : args)
              ty2 ->
                [dSig (dDec (transCTyp env2 C.NoQual ty2) (transName f)) (reverse args)]
        in go env0 ty0 []
  | otherwise =
    let
      stm  = reduce (env0 ^. scope $> tm) ^. reduced
      env1 = env0 & addScope stm
    in
    case stm ^. scoped of
      Proc cs proc0 -> [uncurry (C.DDef (C.Dec voidQ (transName f) [])) (transMkProc env1 cs proc0)]
      _ -> trace ("[WARNING] Skipping compilation of unsupported definition " ++ pretty f) []

transDec :: Env -> Dec -> (Env, [C.Def])
transDec env dec = case {-hDec-} dec of
  Sig d ty tm -> (env & edefs . at d ?~ Ann ty tm, transSig env d ty tm)
  Dat _d _cs ->
    (env, []) -- TODO typedef ? => [C.TEnum (C.EEnm . transCon <$> cs)]
  Assert _a ->
    (env, []) -- could be an assert.. but why?

transProgram :: Program -> C.Prg
transProgram (Program decs) =
  C.PPrg (mapAccumL transDec emptyEnv decs ^.. _2 . each . each)
-- -}
-- -}
-- -}
-- -}
