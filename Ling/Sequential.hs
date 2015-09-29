{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Ling.Sequential where

{-
  programs have parameters
  the meaning is that no synch is expected
  namely if the protocol can "recv" an int on chan c, then
  it means we can read this location, similarily for send.

  TODO, so far only a naive approach is selected

  For each external location either:
    Single read
    Single write
    Read then write
-}

import Control.Lens hiding (op,Empty)

import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Ling.Utils
import Ling.Print
import Ling.Print.Instances ()
import Ling.Session
import Ling.Proc
import Ling.Norm

data Status = Full | Empty deriving (Eq,Read,Show)

toStatus :: Maybe () -> Status
toStatus Nothing    = Empty
toStatus (Just  ()) = Full

fromStatus :: Status -> Maybe ()
fromStatus Empty = Nothing
fromStatus Full  = Just ()

data Location
  = Root Channel
  | Proj Location Int
  deriving (Read,Show,Ord,Eq)

data Env = Env { _chans   :: Map Channel (Location, RSession)
               , _locs    :: Map Location ()
               , _writers :: Map Location Channel }
               -- writers ^. at l == Just c
               -- means that the process owning c was the
               -- last one to write at location l.
  deriving (Show)

$(makeLenses ''Env)

transErr :: Print a => String -> a -> b
transErr msg v = error $ msg ++ "\n" ++ pretty v

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty

addChans :: [(Channel, (Location, RSession))] -> Env -> Env
addChans xys = chans %~ Map.union (Map.fromList xys)

rmChan :: Channel -> Env -> Env
rmChan c = chans . at c .~ Nothing

(!) :: Env -> Channel -> (Location, RSession)
env ! i = fromMaybe err (env ^. chans . at i)
  where err = error $ "lookup/env " ++ show i ++ " in "
                   ++ show (map unName (Map.keys (env ^. chans)))

addLoc :: (Location, Status) -> Env -> Env
addLoc (l, s) = locs . at l .~ fromStatus s

addLocs :: [(Location, Status)] -> Env -> Env
addLocs = flip (foldrOf each addLoc)

{-
statusStep :: Status -> Status
statusStep Full  = Empty
statusStep Empty = Full
-}

mnot :: a -> Maybe a -> Maybe a
mnot a Nothing = Just a
mnot _ Just{}  = Nothing

actEnv :: Channel -> Env -> Env
actEnv c env = env & chans   . at c . mapped . _2 %~ mapR sessionStep
                   & locs    . at l %~ mnot ()
                   & writers . at l %~ mnot c
  where l = fst (env!c)

sessionsStatus :: (Session -> Status) -> Location -> Sessions -> [(Location,Status)]
sessionsStatus dflt l ss =
  [ ls
  | (i,s) <- zip [0..] (flatSessions ss)
  , ls <- sessionStatus dflt (Proj l i) s ]

sessionStatus :: (Session -> Status) -> Location -> Session -> [(Location,Status)]
sessionStatus dflt l x = case x of
  Ten ss -> sessionsStatus dflt l ss
  Par ss -> sessionsStatus dflt l ss
  Seq ss -> sessionsStatus dflt l ss
  _      -> [(l, dflt x)]

rsessionStatus :: (Session -> Status) -> Location -> RSession -> [(Location,Status)]
rsessionStatus dflt l r@(Repl s t) =
  case t of
    Lit 1 -> sessionStatus  dflt l  s
    _     -> sessionsStatus dflt l [r]

statusAt :: Channel -> Env -> Maybe Status
statusAt c env
  | Just c == d = Nothing -- We were the last one to write so we're not ready
  | otherwise   = Just s
  where
    l = fst (env ! c)
    s = env ^. locs . at l . to toStatus
    d = env ^. writers . at l

-- TODO generalize by looking deeper at what is ready now
isReady :: Env -> [Pref] -> Maybe ([Pref], [Pref])
isReady _ [] = error "isReady: impossible"
isReady env (pref : prefs)
  | isReadyPref env pref = Just ([pref], prefs)
  | otherwise            = Nothing

isReadyPref :: Env -> Pref -> Bool
isReadyPref env pref =
  case pref of
    Split{}    -> True
    Nu{}       -> True
    Ax{}       -> True
    -- `At` is considered non-ready. Therefor we cannot put
    -- a process like (@p0() | @p1()) in sequence.
    At{}       -> False
    Send c _   -> statusAt c env == Just Empty
    Recv c _   -> statusAt c env == Just Full
    NewSlice{} -> error "isReadyPref: IMPOSSIBLE"

transSplit :: Channel -> [ChanDec] -> Env -> Env
transSplit c dOSs env =
  rmChan c $
  addChans [ (d, (Proj l n, one (projSession (fromIntegral n) (unRepl session))))
           | (d, n) <- zip ds [(0 :: Int)..] ] env
  where (l, session) = env ! c
        ds = map _argName dOSs

transProc :: Env -> Proc -> (Env -> Proc -> r) -> r
transProc env (prefs `Act` procs) k =
  transAct env prefs procs k

-- prefixes about different channels can be reordered
transAct :: Env -> [Pref] -> [Proc] -> (Env -> Proc -> r) -> r
transAct env prefs0 procs k =
  case prefs0 of
    []         -> transProcs env (filter0s procs) [] k
    pref:prefs -> transAct (transPref pref env) prefs procs $ \env' proc' ->
                  k env' ([pref] `actP` [proc'])

unRepl :: RSession -> Session
unRepl (Repl s (Lit 1)) = s
unRepl r                = transErr "unRepl: unexpected replicated session" r

transPref :: Pref -> Env -> Env
transPref pref =
  case pref of
    Nu (Arg c0 c0ORS) (Arg c1 c1ORS) ->
      let c0OS = unRepl <$> c0ORS
          c1OS = unRepl <$> c1ORS
          Just (c0S , c1S) = extractDuals (c0OS, c1OS)
          l = Root c0
      in
      addLocs  (sessionStatus (const Empty) l c0S) .
      addChans [(c0,(l,one c0S)),(c1,(l,one c1S))]
    Split _ c ds ->
      transSplit c ds
    Send c _ ->
      actEnv c
    Recv c _ ->
      actEnv c
    NewSlice{} ->
      id
    Ax{} ->
      id
    At{} ->
      id

-- Assumption input processes should not have zeros (filter0s)
transProcs :: Env -> [Proc] -> [Proc] -> (Env -> Proc -> r) -> r
transProcs env []       []      k = k env zeroP
transProcs _   []       waiting _ = transErr "transProcs: impossible all the processes are stuck:" waiting
transProcs env [p]      []      k = transProc env p k
transProcs env (p0:p0s) waiting k =
  case p0 of
    prefs@(pref:_) `Act` procs0 ->
      case () of
        _ | NewSlice{} <- pref ->
          transAct env prefs procs0 $ \env' p' ->
            transProcs env' (p0s ++ reverse waiting) [] $ \env'' ps' ->
              k env'' (p' `parP` ps')
        _ | Just (readyPis,restPis) <- isReady env prefs ->
          transAct env readyPis (p0s ++ reverse waiting ++ [restPis `actP` procs0]) k
        _ ->
          transProcs env p0s (p0 : waiting) k

    Act [] _procs0 ->
      error "transProcs: impossible" -- filter0s prevents that

transDec :: Dec -> Dec
transDec x = case x of
  Sig d oty (Just (Proc cs proc)) -> transProc env proc (const $ Sig d oty . Just . Proc cs)
    where
      decSt Snd{} = Empty
      decSt Rcv{} = Full
      decSt End{} = Empty
      decSt _     = error "transDec.decSt: impossible"
      env = addLocs  [ ls          | Arg c (Just s) <- cs, ls <- rsessionStatus decSt (Root c) s ] $
            addChans [ (c, (l, s)) | Arg c (Just s) <- cs, let l = Root c ]
            emptyEnv
  Dat{} -> x
  Sig{} -> x

transProgram :: Program -> Program
transProgram (Program decs) = Program (map transDec decs)
-- -}
-- -}
-- -}
-- -}
