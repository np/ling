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

import Prelude hiding (log)
import Control.Lens hiding (op)

import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import Ling.Utils
import Ling.Print
import Ling.Session
import Ling.Norm
import qualified MiniC.Abs as C
import qualified MiniC.Print as C

type ATyp = (C.Typ, [C.Arr])
type AQTyp = (C.QTyp, [C.Arr])

voidQ :: C.QTyp
voidQ = C.QTyp C.NoQual C.TVoid

tPtr :: ATyp -> ATyp
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

type EVar = Name

data Env =
  Env { _locs  :: Map Channel C.LVal
      , _evars :: Map EVar C.Ident
      , _types :: Set Name
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
primTypes = l2s (Name "Vec" : Map.keys basicTypes)

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty primTypes

addChans :: [(Name, C.LVal)] -> Env -> Env
addChans xys env = env & locs %~ Map.union (Map.fromList xys)

rmChan :: Channel -> Env -> Env
rmChan c env = env & locs . at c .~ Nothing

addEVar :: Name -> C.Ident -> Env -> Env
addEVar x y env
  | env ^. evars . hasKey x = error $ "addEVar/IMPOSSIBLE: " ++ show x ++ " is already bound"
  | otherwise               = env & evars . at x .~ Just y

(!) :: Env -> Name -> C.LVal
env ! i = fromMaybe (error $ "lookup/env " ++ show i ++ " in " ++ show (map unName (Map.keys (env ^. locs))))
                    (env ^. locs . at i)

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

transOp :: EVar -> Maybe (C.Exp -> C.Exp -> C.Exp)
transOp (Name v) = case v of
  "_+_"  -> Just C.Add
  "_+D_" -> Just C.Add
  "_*_"  -> Just C.Mul
  "_*D_" -> Just C.Mul
  "_%_"  -> Just C.Mod
  "_%D_" -> Just C.Mod
  "_-_"  -> Just C.Sub
  "_-D_" -> Just C.Sub
  _      -> Nothing

transEVar :: Env -> EVar -> C.Ident
transEVar env y = fromMaybe (transName y) (env ^. evars . at y)

mkCase :: C.Ident -> [C.Stm] -> C.Branch
mkCase = C.Case . C.EVar

switch :: C.Exp -> [(C.Ident,[C.Stm])] -> C.Stm
switch e brs = C.SSwi e (map (uncurry mkCase) brs)

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
transTerm env x = case x of
  Def f es0
   | env ^. types . contains f -> dummyTyp
   | otherwise ->
     case map (transTerm env) es0 of
       []                             -> C.EVar (transEVar env f)
       [e0,e1] | Just op <- transOp f -> op e0 e1
       es                             -> C.EApp (C.EVar (transName f)) es
  Lit l          -> C.ELit (transLiteral l)
  Lam{}          -> transErr "transTerm/Lam"  x
  Con n          -> C.EVar (transCon n)
  Case t brs     -> switchE (transTerm env t)
                            (map (bimap transCon (transTerm env)) brs)
  Proc{}         -> transErr "transTerm/Proc" x
  TFun{}         -> dummyTyp
  TSig{}         -> dummyTyp
  TProto{}       -> dummyTyp
  TTyp           -> dummyTyp

-- Types are erased to 0
dummyTyp :: C.Exp
dummyTyp = C.ELit (C.LInteger 0)

transProc :: Env -> Proc -> [C.Stm]
transProc env (pref `Dot` procs) = transPref env pref procs

transLVal :: C.LVal -> C.Exp
transLVal (C.LVar x)   = C.EVar x
transLVal (C.LFld l f) = C.EFld (transLVal l) f
transLVal (C.LArw l f) = C.EArw (transLVal l) f
transLVal (C.LArr l i) = C.EArr (transLVal l) i
transLVal (C.LPtr l)   = ePtr   (transLVal l)

ePtr :: C.Exp -> C.Exp
ePtr = C.UOp C.UPtr

transErr :: Print a => String -> a -> b
transErr msg v = error $ msg ++ "\n" ++ pretty v

transErrC :: C.Print a => String -> a -> b
transErrC msg v = error $ msg ++ "\n" ++ C.render (C.prt 0 v)

transProcs :: Env -> [Proc] -> [C.Stm]
transProcs = concatMap . transProc

-- Implement the effect of an action over:
-- * an environment
-- * a list of statements
transAct :: Env -> Act -> (Env, Endom [C.Stm])
transAct env act =
  case act of
    Nu (Arg c0 c0OS) (Arg c1 c1OS) ->
      (env', (sDec typ cid C.NoInit ++))
      where
        s    = log $ extractSession [c0OS, c1OS]
        cid  = transName c0
        l    = C.LVar cid
        typ  = transRSession env s
        env' = addChans [(c0,l),(c1,l)] env
    Split _ c ds ->
      (transSplit c ds env, id)
    Send c expr ->
      (env, (C.SPut (env ! c) (transTerm env expr) :))
    Recv c (Arg x typ) ->
      (addEVar x (transName x) env, (sDec ctyp y cinit ++))
      where
        ctyp  = transCTyp env C.QConst typ
        y     = transName x
        cinit = C.SoInit (transLVal (env!c))
    NewSlice cs t xi ->
      (env', pure . stdFor (transName xi) (transTerm env t))
      where
        i = transName xi
        sliceIf c l | c `elem` cs = C.LArr l (C.EVar i)
                    | otherwise   = l
        env' = env & locs . imapped %@~ sliceIf
                   & addEVar xi i
    Ax{} ->
      transErr "transAct/Ax" act
    At{} ->
      transErr "transAct/At" act

-- The actions in this prefix are in parallel and thus can be reordered
transPref :: Env -> Pref -> [Proc] -> [C.Stm]
transPref env []         = transProcs env
transPref env (act:pref) = actStm . transPref env' pref
    where (env', actStm) = transAct env act

{- stdFor i t body ~~~> for (int i = 0; i < t; i = i + 1) { body } -}
stdFor :: C.Ident -> C.Exp -> [C.Stm] -> C.Stm
stdFor i t =
  C.SFor (C.SDec (C.Dec (C.QTyp C.NoQual C.TInt) i []) (C.SoInit (C.ELit (C.LInteger 0))))
         (C.Lt (C.EVar i) t)
         (C.SPut (C.LVar i) (C.Add (C.EVar i) (C.ELit (C.LInteger 1))))

{- Special case:
   {S}/[S] has the same implementation as S.
   See tupQ -}
transSplit :: Name -> [ChanDec] -> Env -> Env
transSplit c dOSs env = rmChan c $ addChans newChans env
  where
    lval = env ! c
    ds   = map _argName dOSs
    newChans =
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

allEq :: Eq a => [a] -> Bool
allEq []     = False
allEq (t:ts) = all (== t) ts

unionT :: [ATyp] -> ATyp
unionT ts
  | allEq ts  = head ts
  | otherwise = (C.TUni [ C.FFld t (uniI i) arrs | (i,(t,arrs)) <- zip [0..] ts ], [])

unionQual :: C.Qual -> C.Qual -> C.Qual
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

transTyp :: Env -> Typ -> ATyp
transTyp env e0 = case e0 of
  Def x es
    | Just t <- Map.lookup x basicTypes -> (t, [])
    | otherwise ->
    case (unName x, es) of
      -- ("Vec", [a,e]) -> tArr (transTyp env a) (transTerm env e)
      ("Vec", [a,_e]) -> tPtr (transTyp env a)
      _               -> tVoidPtr -- WARNING transError "transTyp: " e0
  TTyp{}   -> tInt -- <- types are erased to 0
  Case{}   -> transErr "transTyp: Case" e0
  TProto{} -> transErr "transTyp: TProto" e0
  TFun{}   -> transErr "transTyp: TFun" e0
  TSig{}   -> transErr "transTyp: TSig" e0 -- TODO struct ?
  Lam{}    -> transErr "transTyp: Not a type: Lam" e0
  Lit{}    -> transErr "transTyp: Not a type: Lit" e0
  Con{}    -> transErr "transTyp: Not a type: Con" e0
  Proc{}   -> transErr "transTyp: Not a type: Proc" e0

transCTyp :: Env -> C.Qual -> Typ -> AQTyp
transCTyp env qual = (_1 %~ C.QTyp qual) . transTyp env

{-
mapQTyp :: (C.Typ -> C.Typ) -> C.QTyp -> C.QTyp
mapQTyp f (C.QTyp  q t) = C.QTyp q (f t)
-}

mapAQTyp :: (ATyp -> ATyp) -> AQTyp -> AQTyp
mapAQTyp f (C.QTyp  q t , arrs) = (C.QTyp q t', arrs')
  where (t', arrs') = f (t, arrs)

transSession :: Env -> Session -> AQTyp
transSession env x = case x of
  End      -> tupQ []
  Snd a s  -> unionQ [transCTyp env C.NoQual a, transSession env s]
  Rcv a s  -> unionQ [transCTyp env C.QConst a, transSession env s]
  Par ss   -> tupQ (transSessions env ss)
  Ten ss   -> tupQ (transSessions env ss)
  Seq ss   -> tupQ (transSessions env ss)
  Atm _ n  -> transErr "Cannot compile an abstract session: " n

transRSession :: Env -> RSession -> AQTyp
transRSession env (Repl s a) = case a of
  Lit (LInteger 1) -> transSession env s
  _                -> mapAQTyp (\t -> tArr t (transTerm env a)) (transSession env s)

transSessions :: Env -> Sessions -> [AQTyp]
transSessions = map . transRSession

isPtrTyp :: C.Typ -> Bool
isPtrTyp (C.TPtr _) = True
isPtrTyp _          = False

isPtrQTyp :: AQTyp -> Bool
isPtrQTyp (C.QTyp _ t, []) = isPtrTyp t
isPtrQTyp _                = True

-- Turns a type into a pointer unless it is one already.
mkPtrTyp :: AQTyp -> (AQTyp, C.LVal -> C.LVal)
mkPtrTyp ctyp
  | isPtrQTyp ctyp = (ctyp, id)
  | otherwise      = (mapAQTyp tPtr ctyp, C.LPtr)

transChanDec :: Env -> ChanDec -> (C.Dec , (Channel, C.LVal))
transChanDec env (Arg c (Just session)) =
    (dDec ctyp d, (c, trlval (C.LVar d)))
  where
    d              = transName c
    (ctyp, trlval) = mkPtrTyp (transRSession env session)
transChanDec _   (Arg c Nothing)
  = transErr "transChanDec: TODO No Session for channel:" c

transSig :: Env -> Name -> Maybe Typ -> Maybe Term -> C.Def
transSig env0 f _ty0 (Just t) =
  case t of
    Proc cs proc ->
      C.DDef (C.Dec voidQ (transName f) [])
             (map fst news)
             (transProc env proc)
      where
        news = map (transChanDec env0) cs
        env  = addChans (map snd news) env0
    _ -> transErr "transSig: TODO unsupported def" t
-- Of course this does not properly handle dependent types
transSig env0 f (Just ty0) Nothing = case ty0 of
  TFun{} -> go env0 [] ty0 where
    go env args t1 = case t1 of
      TFun (Arg n s) t -> go (addEVar n (transName n) env)
                             (dDec (transCTyp env C.QConst s) (transName n) : args)
                             t
      _                -> C.DSig (dDec (transCTyp env C.NoQual t1) (transName f))
                                 (reverse args)
  _ -> C.DDec (dDec (transCTyp env0 C.NoQual ty0) (transName f))
transSig _ _ Nothing Nothing = error "IMPOSSIBLE transSig no sig nor def"

transDec :: Env -> Dec -> [C.Def]
transDec env x = case x of
  Sig d ty tm -> [transSig env d ty tm]
  Dat _d _cs ->
    [] -- TODO typedef ? => [C.TEnum (map (C.EEnm . transCon) cs)]
  Assert _a ->
    [] -- could be an assert.. but why?

transProgram :: Program -> C.Prg
transProgram (Program decs) = C.PPrg (transDec emptyEnv =<< decs)
-- -}
-- -}
-- -}
-- -}
