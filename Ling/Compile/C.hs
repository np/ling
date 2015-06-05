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
import Control.Lens hiding (act,acts,op)

import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import Ling.Abs (Name(Name))
import Ling.Utils
import Ling.Print
import Ling.Print.Instances ()
import Ling.Session
import Ling.Norm
import qualified MiniC.Abs as C

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
eFld (C.EPtr l) = C.EArw l
eFld         l  = C.EFld l

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
  [("Int", C.TInt),("Double", C.TDouble)] ]

primTypes :: Set Name
primTypes = l2s (Name "Vec" : Map.keys basicTypes)

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty primTypes

addChans :: [(Name, C.LVal)] -> Env -> Env
addChans xys env = env & locs %~ Map.union (Map.fromList xys)

rmChan :: Channel -> Env -> Env
rmChan c env = env & locs . at c .~ Nothing

addEVar :: Name -> C.Ident -> Env -> Env
addEVar x y env = env & evars . at x .~ Just y

(!) :: Env -> Name -> C.LVal
env ! i = fromMaybe (error $ "lookup/env " ++ show i ++ " in " ++ show (map unName (Map.keys (env ^. locs))))
                    (env ^. locs . at i)

transName :: Name -> C.Ident
transName (Name x) = C.Ident (concatMap f x ++ "_lin") where
  f '#'  = "__"
  f '\'' = "__"
  f '+'  = "_plus_"
  f '*'  = "_times_"
  f '/'  = "_div_"
  f '-'  = "_sub_"
  f  c   = [c]

transOp :: EVar -> Maybe C.Op
transOp (Name v) = case v of
  "_+_"  -> Just (C.Op "+")
  "_+D_" -> Just (C.Op "+")
  "_*_"  -> Just (C.Op "*")
  "_*D_" -> Just (C.Op "*")
  "_%_"  -> Just (C.Op "%")
  "_%D_" -> Just (C.Op "%")
  "_-_"  -> Just (C.Op "-")
  "_-D_" -> Just (C.Op "-")
  _      -> Nothing

transEVar :: Env -> EVar -> C.Ident
transEVar env y = fromMaybe (transName y) (env ^. evars . at y)

transTerm :: Env -> Term -> C.Exp
transTerm env x = case x of
  Def f es0
   | env ^. types . contains f -> C.ELit 0 -- <- types are erased to 0
   | otherwise ->
     case map (transTerm env) es0 of
       []                             -> C.EVar (transEVar env f)
       [e0,e1] | Just op <- transOp f -> C.EInf e0 op e1
       es                             -> C.EApp (transName f) es
  Lit n          -> C.ELit n
  Proc{}         -> transErr "transTerm/Proc" x
  TFun{}         -> C.ELit 0 -- <- types are erased to 0
  TSig{}         -> C.ELit 0 -- <- types are erased to 0
  TProto{}       -> C.ELit 0 -- <- types are erased to 0
  TTyp            -> C.ELit 0 -- <- types are erased to 0

transProc :: Env -> Proc -> [C.Stm]
transProc env x = case x of
  Ax{} ->
    transErr "transProc/Ax" x
  At{} ->
    transErr "transProc/At" x
  acts `Act` procs ->
    transAct env acts procs
  NewSlice cs t xi p ->
    [stdFor i (transTerm env t) (transProc env' p)]
    where
      i = transName xi
      sliceIf c l | c `elem` cs = C.LArr l (C.EVar i)
                  | otherwise   = l
      env' = env & locs . imapped %@~ sliceIf
                 & addEVar xi i

transLVal :: C.LVal -> C.Exp
transLVal (C.LVar x)   = C.EVar x
transLVal (C.LFld l f) = C.EFld (transLVal l) f
transLVal (C.LArw l f) = C.EArw (transLVal l) f
transLVal (C.LArr l i) = C.EArr (transLVal l) i
transLVal (C.LPtr l)   = C.EPtr (transLVal l)

transErr :: Print a => String -> a -> b
transErr msg v = error $ msg ++ "\n" ++ pretty v

transProcs :: Env -> [Proc] -> [C.Stm]
transProcs = concatMap . transProc

-- prefixes about different channels can be reordered
transAct :: Env -> [Pref] -> [Proc] -> [C.Stm]
transAct env []           procs = transProcs env procs
transAct env (pref:prefs) procs =
  case pref of
    Nu (Arg c0 c0OS) (Arg c1 c1OS) ->
      sDec typ cid C.NoInit ++ transAct env' prefs procs
      where
        s    = log $ extractSession [c0OS, c1OS]
        cid  = transName c0
        l    = C.LVar cid
        typ  = transRSession env s
        env' = addChans [(c0,l),(c1,l)] env
    Split _ c ds ->
      transAct (transSplit c ds env) prefs procs
    Send c expr ->
      C.SPut (env ! c) (transTerm env expr) :
      transAct env prefs procs
    Recv c (Arg x typ) ->
      sDec ctyp y (C.SoInit (transLVal l)) ++
      transAct (addEVar x y env) prefs procs
      where
        l    = env ! c
        ctyp = transCTyp env C.QConst typ
        y    = transName x

{- stdFor i t body ~~~> for (int i = 0; i < t; i = i + 1) { body } -}
stdFor :: C.Ident -> C.Exp -> [C.Stm] -> C.Stm
stdFor i t =
  C.SFor (C.SDec (C.Dec (C.QTyp C.NoQual C.TInt) i []) (C.SoInit (C.ELit 0)))
         (C.EInf (C.EVar i) (C.Op "<") t)
         (C.SPut (C.LVar i) (C.EInf (C.EVar i) (C.Op "+") (C.ELit 1)))

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
  TProto{} -> transErr "transTyp: TProto" e0
  TFun{}   -> transErr "transTyp: TFun" e0
  TSig{}   -> transErr "transTyp: TSig" e0 -- TODO struct ?
  Lit{}    -> transErr "transTyp: Not a type: Lit" e0
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
  Lit 1 -> transSession env s
  _     -> mapAQTyp (\t -> tArr t (transTerm env a)) (transSession env s)

transSessions :: Env -> Sessions -> [AQTyp]
transSessions = map . transRSession

-- We
isPtrTyp :: C.Typ -> Bool
isPtrTyp (C.TPtr _) = True
isPtrTyp _           = False

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

-- Of course this does not properlly handle dependent types
transSig :: Env -> Name -> Typ -> C.Def
transSig env0 f t0 = case t0 of
  TFun{} -> go env0 [] t0 where
    go env args t1 = case t1 of
      TFun (Arg n s) t -> go (addEVar n (transName n) env)
                             (dDec (transCTyp env C.QConst s) (transName n) : args)
                             t
      _                -> C.DSig (dDec (transCTyp env C.NoQual t1) (transName f))
                                 (reverse args)
  _ -> C.DDec (dDec (transCTyp env0 C.NoQual t0) (transName f))

transDec :: Env -> Dec -> [C.Def]
transDec env x = case x of
  Sig d t -> [transSig env d t]
  Dec d cs proc ->
    [C.DDef (C.Dec voidQ (transName d) [])
            (map fst news)
            (transProc env' proc)]
    where
      news = map (transChanDec env) cs
      env' = addChans (map snd news) env

transProgram :: Program -> C.Prg
transProgram (Program decs) = C.PPrg (transDec emptyEnv =<< decs)
-- -}
-- -}
-- -}
-- -}
