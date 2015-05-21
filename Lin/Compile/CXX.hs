{-# LANGUAGE TemplateHaskell #-}
module Lin.Compile.CXX where

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

import Control.Lens hiding (act,acts,op)

import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import Lin.Abs (Name(Name))
import Lin.Utils
import Lin.Session
import Lin.View
import Lin.Proc
import qualified Lin.Norm   as N
import qualified MiniCXX.Abs as C
import Debug.Trace

decNoInit :: C.QTyp -> C.Ident -> [C.Stm]
decNoInit C.QVoid _ = []
decNoInit typ cid   = [C.SDec (C.DDec typ cid) C.NoInit]

voidQ :: C.QTyp
voidQ = C.QVoid

data RW = Read | Write deriving (Eq,Read,Show)

type EVar      = Name

data CChanInfo =
  CChanInfo { _chanLVal :: C.LVal
            , _chanQTyp :: C.QTyp
            , _chanSess :: N.Session
            }
  deriving (Show)

$(makeLenses ''CChanInfo)

data Env =
  Env { _chans :: Map Channel CChanInfo
      , _rws   :: Map C.LVal RW
      , _evars :: Map EVar C.Ident
      , _types :: Set Name
      }
  deriving (Show)

$(makeLenses ''Env)

primTypes :: Set Name
primTypes = l2s (map Name ["Vec", "Int"])

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty primTypes

addChan :: Name -> CChanInfo -> Env -> Env
addChan x y env = env & chans . at x .~ Just y

addChans :: [(Name, CChanInfo)] -> Env -> Env
addChans xys env = env & chans %~ Map.union (Map.fromList xys)

chanInfo :: Name -> N.Session -> (C.Ident, C.QTyp, CChanInfo)
chanInfo c s = (cid, typ, info)
  where cid  = transName c
        typ  = transSession s
        info = CChanInfo (C.LVar cid) typ s

mkChanInfo :: (Name, Name, N.Session) -> [(Name, CChanInfo)]
mkChanInfo (c0, c1, session) = [(c0, info), (c1, info)]
  where (_,_,info) = chanInfo c0 session

addChans' :: [(Name, Name, N.Session)] -> Env -> Env
addChans' = addChans . concatMap mkChanInfo

rmChan :: Channel -> Env -> Env
rmChan c env = env & chans . at c .~ Nothing

addEVar :: Name -> C.Ident -> Env -> Env
addEVar x y env = env & evars . at x .~ Just y

(!) :: Env -> Name -> CChanInfo
env ! i = fromMaybe (error $ "lookup/env " ++ show i ++ " in " ++ show (map (unName . fst) (Map.toList (env ^. chans))))
                    (env ^. chans . at i)

-- assert env ^. rws . at c == isRW (oppRW rw)
actEnv :: Name -> RW -> Env -> (C.LVal, Env)
actEnv c rw env = (l, env')
  where info = env ! c
        env' = env & rws . at (info ^. chanLVal) .~ Just rw
                   & chans . at c . mapped . chanSess %~ sessionStep
        l = (env' ! c)^.chanLVal -- TODO HERE

transName :: Name -> C.Ident
transName (Name x) = C.Ident x

rwFromSession :: Maybe N.Session -> RW
rwFromSession Nothing  = error "rwFromSession: TODO NoSession"
rwFromSession (Just x) = case x of
  N.End -> error "rwFromSession: N.End"
  N.Snd _ N.End -> Write
  N.Snd _ _    -> error "rwFromSession: N.Snd..."
  N.Rcv _ s
    | isEnd s || isSndEnd s -> Read
    | otherwise -> error "rwFromSession: N.Rcv..."
  N.Par _ -> error "rwFromSession: TODO N.Par"
  N.Ten _ -> error "rwFromSession: TODO N.Ten"
  N.Seq _ -> error "rwFromSession: TODO N.Seq"

transOp :: EVar -> Maybe C.Op
transOp (Name v) = case v of
  "_+_" -> Just C.Plus
  _     -> Nothing

transEVar :: Env -> EVar -> C.Ident
transEVar env y = fromMaybe (error "transEVar") (env ^. evars . at y)

transTerm :: Env -> N.Term -> C.Exp
transTerm env x = case x of
  N.Def f es0
   | env ^. types . contains f -> C.ELit 0 -- <- types are erased to 0
   | otherwise ->
     case map (transTerm env) es0 of
       []                             -> C.EVar (transEVar env f)
       [e0,e1] | Just op <- transOp f -> C.EInf e0 op e1
       es                             -> C.EApp (transName f) es
  N.Lit n          -> C.ELit n
  N.Proc ids proc  -> error "transTerm/Proc" ids proc
  N.Ann e _typ     -> transTerm env e
  N.TFun{}         -> C.ELit 0 -- <- types are erased to 0
  N.TSig{}         -> C.ELit 0 -- <- types are erased to 0
  N.TProto{}       -> C.ELit 0 -- <- types are erased to 0
  N.TTyp            -> C.ELit 0 -- <- types are erased to 0

transProc :: Env -> N.Proc -> [C.Stm]
transProc env x = case viewProc x of
  AxV{} ->
    error $ "transProc" ++ show x
  AtV{} ->
    error $ "transProc" ++ show x
  ActV acts procs ->
    transAct env acts procs

transLVal :: C.LVal -> C.Exp
transLVal (C.LVar x)   = C.EVar x
transLVal (C.LFld l f) = C.EFld (transLVal l) f
transLVal (C.LArr l i) = C.EArr (transLVal l) i

-- prefixes about different channels can be reordered
transAct :: Env -> [N.Pref] -> [N.Proc] -> [C.Stm]
transAct env [] procs = transProcs 0 env procs
transAct env (pref:prefs) procs =
  case pref of
    N.Nu (Arg c0 c0OS) (Arg c1 c1OS) ->
      let session = extractSession [c0OS, c1OS]
          (cid,typ,info) = chanInfo c0 session -- we assume unicity of channel names
          env' = addChans [(c0,info),(c1,info)] env
          -- TODO use addChans'
      in
      decNoInit typ cid ++ transAct env' prefs procs
    N.ParSplit c ds ->
      transAct (transPi c ds env) prefs procs
    N.TenSplit c ds ->
      transAct (transPi c ds env) prefs procs
    N.Send c expr ->
      let (l, env') = actEnv c Read env in
      C.SPut l (transTerm env expr) :
      transAct env' prefs procs
    N.Recv c (Arg x typ) ->
      let (l, env') = actEnv c Write env
          ctyp = transCTyp typ
      in
      C.SDec (C.DDec ctyp y) (C.SoInit (transLVal l)) :
      transAct (addEVar x y env') prefs procs
      where y = transName x
    N.NewSlice _t _x -> error "CXX.transAct/Slice"

transProcs :: Int -> Env -> [N.Proc] -> [C.Stm]
transProcs tries env ps =
  case filter0Vs ps of
    []  -> []
    [p] -> transProc env (unview p)
    (p0@(ActV acts@(_:_) procs0) : procs1) ->
      case isReady env acts of
        Nothing ->
          if tries < 10 then
            transProcs (tries + 1) env (map unview (procs1 ++ [p0])) --- <-- Uhoh termination
          else trace "Prevented non termination" []
        Just (readyPis,restPis) ->
          transAct env readyPis (map unview procs1 ++ [restPis `actP` N.Procs procs0])

    (AtV{} : _) ->
      error "transProcs: AtV"

    -- One should expand the forwarders
    (AxV{} : _) ->
      error "transProcs: AxV"

    (ActV [] _procs0 : _procs1) ->
      error "transProcs: impossible"

tupProj :: Int -> C.QTyp -> C.QTyp
tupProj n (C.QTyp q (C.TTup ts))
  | n < length ts = C.QTyp q (ts !! n)
  | otherwise     = error "tupProj: out of bound"
tupProj _ _ = error "tupProj: not a tuple type"

isWrite, isRead :: Maybe RW -> Bool
isWrite x = isNothing x || x == Just Write
isRead  x = x == Just Read

-- TODO generalize by looking deeper at what is ready now
isReady :: Env -> [N.Pref] -> Maybe ([N.Pref], [N.Pref])
isReady _ [] = error "isReady: impossible"
isReady env (act : acts) =
  case act of
    N.ParSplit{} -> Just ([act], acts) -- error "TODO: float out?"
    N.TenSplit{} -> Just ([act], acts) -- error "TODO: float out?"
    N.Nu{} -> error "TODO: Nu: float out?"
    N.Send c _ ->
      let l = (env ! c) ^. chanLVal in
      if env ^. rws . at l . to isWrite then Just ([act], acts)
      else Nothing
    N.Recv c _ ->
      let l = (env ! c) ^. chanLVal in
      if env ^. rws . at l . to isRead  then Just ([act], acts)
      else Nothing
    N.NewSlice{} -> error "TODO: isReady NewSlice"

{- Special cases, {}/[] are implemented as void and
   {S}/[S] as the implementation for S.
   See tupQ -}
transPi :: Name -> [N.ChanDec] -> Env -> Env
transPi c dOSs env =
  rmChan c $
  case ds of
    []  -> env
    [d] -> addChans [ (d, CChanInfo lval typ (projSession 0 session)) ] env
    _   ->
      addChans [ (d, CChanInfo lval'  typ' ses')
               | (d,n) <- zip ds [0..]
               , let lval' = C.LFld lval (C.Ident ("proj" ++ show (n :: Int)))
               , let ses'  = projSession (fromIntegral n) session
               , let typ'  = tupProj n typ --- TODO using session instead of typ is probably better
               ] env
  where (CChanInfo lval typ session) = env ! c
        ds = map _argName dOSs

unionT :: C.Typ -> C.Typ -> C.Typ
unionT t u
  | t == u    = t
  | otherwise = C.TUni [t,u]

unionQual :: C.Qual -> C.Qual -> C.Qual
unionQual C.QConst C.QConst = C.QConst
unionQual _        _        = C.NoQual

unionQuals :: [C.Qual] -> C.Qual
unionQuals = foldr unionQual C.QConst

unionQ :: C.QTyp -> C.QTyp -> C.QTyp
unionQ C.QVoid q = q
unionQ q C.QVoid = q
unionQ (C.QTyp q0 t0) (C.QTyp q1 t1) = C.QTyp (unionQual q0 q1) (unionT t0 t1)

{- See transPi about these two special cases -}
tupQ :: [C.QTyp] -> C.QTyp
tupQ [] = voidQ
tupQ [t] = t
tupQ ts = C.QTyp (unionQuals [ q | C.QTyp q _ <- ts ])
                 (C.TTup     [ t | C.QTyp _ t <- ts ])

transTyp :: N.Typ -> C.Typ
transTyp e0 = case e0 of
  N.Def x es ->
    case (unName x, es) of
      ("Int", [])    -> C.TInt
      ("Vec", [a,e]) -> C.TArr (transTyp a) (transTerm emptyEnv e)
      _              -> error $ "transTyp: " ++ show e0
  N.Ann e _  -> transTyp e
  N.TTyp{}   -> C.TInt -- <- types are erased to 0
  N.TProto{} -> error "transTyp: N.TProto"
  N.Lit{}    -> error "transTyp: N.Lit"
  N.Proc{}   -> error "transTyp: N.Proc"
  N.TFun{}   -> error "transTyp: N.TFun"
  N.TSig{}   -> error "transTyp: N.TSig" -- TODO tuple ?

transCTyp :: N.Typ -> C.QTyp
transCTyp = C.QTyp C.QConst . transTyp

transSession :: N.Session -> C.QTyp
transSession x = case x of
  N.End      -> voidQ
  N.Snd a s  -> unionQ (C.QTyp C.NoQual (transTyp a)) (transSession s)
  N.Rcv a s  -> unionQ (C.QTyp C.QConst (transTyp a)) (transSession s)
  N.Par ss   -> tupQ (transSessions ss)
  N.Ten ss   -> tupQ (transSessions ss)
  N.Seq ss   -> tupQ (transSessions ss)

transRSession :: N.RSession -> [C.QTyp]
transRSession (N.Repl s a) = case a of
  N.Lit n -> replicate (fromInteger n) (transSession s)
  _       -> error "transRSession/Repl: only integer literals are supported"

transSessions :: N.Sessions -> [C.QTyp]
transSessions = concatMap transRSession

transChanDec :: N.ChanDec -> C.Dec
transChanDec (Arg c (Just session)) = C.DDec (transSession session) (transName c)
transChanDec (Arg _ Nothing)        = error "transChanDec: TODO No Session"

-- Of course this does not properlly handle dependent types
transSig :: Name -> [C.Dec] -> N.Typ -> C.Def
transSig f args e0 = case e0 of
  N.TFun (Arg n s) t -> transSig f (C.DDec (transCTyp s) (transName n) : args) t
  _                 -> C.DSig (C.DDec (C.QTyp C.NoQual (transTyp e0)) (transName f))
                              (reverse args)

transDec :: N.Dec -> [C.Def]
transDec x = case x of
  N.Sig _d _t -> [] -- transSig d [] t
  N.Dec d cs proc ->
    [C.DDef (C.DDec voidQ (transName d))
            (map transChanDec cs)
            (transProc env proc)]
    where
      env = foldr (.) id [ snd . actEnv c (rwFromSession s) | Arg c s <- cs ] $
            addChans' [ (c, c, s) | Arg c (Just s) <- cs ] emptyEnv

transProgram :: N.Program -> C.Prg
transProgram x = case x of
  N.Program decs -> C.PPrg (transDec =<< decs)
-- -}
-- -}
-- -}
-- -}
