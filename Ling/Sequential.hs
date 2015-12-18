{-# LANGUAGE TemplateHaskell, RankNTypes, LambdaCase #-}
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

import qualified Data.Map as Map
import Ling.Prelude
import Ling.Print
import Ling.Session
import Ling.Proc
import Ling.Norm
import Ling.Rename
import Ling.Scoped (Scoped(Scoped))
import Ling.Defs (pushDefs)
import Ling.Reduce (reduceTerm)

data Status = Full | Empty deriving (Eq,Read,Show)

status :: Iso' (Maybe ()) Status
status = iso toStatus fromStatus
  where
    toStatus Nothing    = Empty
    toStatus (Just  ()) = Full
    fromStatus Empty = Nothing
    fromStatus Full  = Just ()

data Location
  = Root Channel
  | Proj Location Int
  | Next Location
  deriving (Read,Show,Ord,Eq)

data Env = Env { _chans   :: Map Channel (Location, RSession)
               , _edefs   :: Defs
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
emptyEnv = Env ø ø ø ø

addChans :: [(Channel, (Location, RSession))] -> Endom Env
addChans xys = chans %~ Map.union (l2m xys)

rmChan :: Channel -> Endom Env
rmChan c = chans .\\ c

(!) :: Env -> Channel -> (Location, RSession)
(!) = lookupEnv _Name chans

addLoc :: (Location, Status) -> Endom Env
addLoc (l, s) = locs . at l . status .~ s

addLocs :: [(Location, Status)] -> Endom Env
addLocs = composeMapOf each addLoc

{-
statusStep :: Endom Status
statusStep Full  = Empty
statusStep Empty = Full
-}

actEnv :: Channel -> Endom Env
actEnv c env = env & chans   . at c . mapped %~ bimap Next (mapR sessionStep)
                   & locs    . at l %~ mnot ()
                   & writers . at l %~ mnot c
  where l = fst (env!c)

sessionsStatus :: Defs -> (RW -> Status) -> Location -> Sessions -> [(Location,Status)]
sessionsStatus defs dflt l ss =
  [ ls
  | (i,s) <- zip [0..] (unsafeFlatSessions ss)
  , ls <- sessionStatus defs dflt (Proj l i) s ]

sessionStatus :: Defs -> (RW -> Status) -> Location -> Session -> [(Location,Status)]
sessionStatus defs dflt l = \case
  Array _ ss -> sessionsStatus defs dflt l ss
  IO rw _ s  -> (l, dflt rw) : sessionStatus defs dflt (Next l) s
  TermS p t ->
    case reduceTerm' defs t of
      TSession s -> sessionStatus defs dflt l (sessionOp p s)
      t'         -> trace ("[WARNING] Skipping abstract session " ++ pretty t')
                    [(l, Empty)]

rsessionStatus :: Defs -> (RW -> Status) -> Location -> RSession -> [(Location,Status)]
rsessionStatus defs dflt l sr@(s `Repl` r)
  | litR1 `is` r = sessionStatus  defs dflt l s
  | otherwise    = sessionsStatus defs dflt l [sr]

statusAt :: Channel -> Env -> Maybe Status
statusAt c env
  | Just c == d = Nothing -- We were the last one to write so we're not ready
  | otherwise   = Just s
  where
    l = fst (env ! c)
    s = env ^. locs . at l . status
    d = env ^. writers . at l

-- TODO generalize by looking deeper at what is ready now
splitReady :: Env -> Pref -> (Pref, Pref)
splitReady env = bimap Prll Prll . partition (isReady env) . _unPrll

reduceProc :: Defs -> Endom Proc
reduceProc defs = \case
  Act act -> reduceAct defs act
  proc0 `Dot` proc1 -> reduceProc defs proc0 `dotP` reduceProc defs proc1 -- TODO add the LetA defs from proc0
  Procs procs -> procs ^. each . to (reduceProc defs)
  NewSlice cs t x p -> NewSlice cs t x (reduceProc defs p)

reduceAct :: Defs -> Act -> Proc
reduceAct defs act =
  case act of
    At t p ->
      case p of
        ChanP (ChanDec c _ _) ->
          case reduceTerm' defs t of
            Proc cs proc0 ->
              case cs of
                [ChanDec c' _ _] ->
                  rename1 (c', c) proc0
                _ -> transErr "reduceAct/At/Non single proc" act
            _ -> transErr "reduceAct/At/Non Proc" act
        _ -> transErr "reduceAct/At/Non ChanP" act
    _ -> Act act

isReady :: Env -> Act -> Bool
isReady env = \case
  Split{}    -> True
  Nu{}       -> True
  Ax{}       -> True
  LetA{}     -> True
  -- `At` is considered non-ready. Therefor we cannot put
  -- a process like (@p0() | @p1()) in sequence.
  At{}       -> False
  Send c _   -> statusAt c env == Just Empty
  Recv c _   -> statusAt c env == Just Full

transSplit :: Channel -> [ChanDec] -> Endom Env
transSplit c dOSs env =
  rmChan c $
  addChans [ (d, (Proj l n, oneS (projSessions (integral # n) sessions)))
           | (d, n) <- zip ds [(0 :: Int)..] ] env
  where (l, session) = env ! c
        sessions = session ^? to unRepl . _Array . _2 {-. to unsafeFlatSessions-} ?| error "transSplit: expected to split an array"
        ds = dOSs ^.. each . cdChan

transProc :: Env -> Proc -> (Env -> Proc -> r) -> r
transProc env proc0 = transProcs env [proc0] []

-- All these prefixes can be reordered as they are in parallel
transPref :: Env -> Pref -> [Proc] -> (Env -> Proc -> r) -> r
transPref env (Prll pref0) procs k =
  case pref0 of
    []       -> transProcs env procs [] k
    act:pref -> transPref (transAct (env ^. edefs) act env) (Prll pref) procs $ \env' proc' ->
                  k env' ((act {-& _Nu %~ transNu
                               & _Split . _1 .~ SeqK-}) `dotP` proc')

{-
-- This could be part of the Dual class, a special Seq operation could also
-- be part of DualOp
transSession :: Endom Session
transSession = \case
  Array _ ss -> Array SeqK (ss & list . rsession %~ transSession)
  IO _ a s   -> IO Write a (transSession s)
  TermS _ t -> TermS LogOp t

transNu :: Endom ([Term], TraverseKind, [ChanDec])
transNu (anns, k, cds)
  | TenK <- k =
      (anns, SeqK, cds & _head . cdSession . _Just . rsession %~ transSession
                       & _tail . each . cdSession .~ Nothing)
  | otherwise = (anns, k, cds)
-}

transAct :: Defs -> Act -> Endom Env
transAct defs act =
  case act of
    Nu _ _ [] ->
      id
    Nu _ _ cds0 ->
      let
        cds1 = [ Arg c cOS | ChanDec c _ cOS <- cds0 ]
        cds2@(Arg c0 c0S:_) = cds1 & each . argBody . _Just %~ unRepl
                                   & unsafePartsOf (each . argBody) %~ extractDuals
        l = Root c0
      in
      addLocs  (sessionStatus defs (const Empty) l c0S) .
      addChans [(c,(l,oneS cS)) | Arg c cS <- cds2]
    Split _ c ds ->
      transSplit c ds
    Send c _ ->
      actEnv c
    Recv c _ ->
      actEnv c
    Ax{} ->
      id
    At{} ->
      id
    LetA ldefs ->
      edefs <>~ ldefs

transProcs :: Env -> [Proc] -> [Proc] -> (Env -> Proc -> r) -> r
transProcs env p0s waiting k =
  case p0s of
    [] ->
      case waiting of
        []     -> k env ø
        [p]    -> transProcs env [p] [] k
        _   -> transErr "All the processes are stuck" waiting

    p0':ps ->
      let p0 = reduceProc (env ^. edefs) p0' in
      case p0 of
        NewSlice cs t x p ->
          transProc env p $ \env' p' ->
            transProcs env' (ps ++ reverse waiting) [] $ \env'' ps' ->
              k env'' (NewSlice cs t x p' `dotP` ps')

        Procs (Prll ps0) ->
          transProcs env (ps0 ++ ps) waiting k

        _ | Just (pref, p1) <- p0 ^? _PrefDotProc ->
            case () of
            _ | pref == ø -> transErr "transProcs: pref == ø IMPOSSIBLE" p0
            _ | (readyPis@(Prll(_:_)),restPis) <- splitReady env pref ->
              transPref env readyPis (ps ++ reverse waiting ++ [restPis `dotP` p1]) k

            _ | null ps && null waiting ->
              trace ("[WARNING] Sequencing a non-ready prefix " ++ pretty pref)
              transPref env pref [p1] k

            _ ->
              transProcs env ps (p0 : waiting) k

        _ ->
          transProcs env ps (p0 : waiting) k

initEnv :: Defs -> [ChanDec] -> Env
initEnv gdefs cs =
  emptyEnv
    & edefs .~ gdefs
    & addLocs  [ ls | ChanDec c _ (Just s) <- cs
               , ls <- rsessionStatus gdefs decSt (Root c) s ]
    & addChans [ (c, (Root c, s)) | ChanDec c _ (Just s) <- cs ]
  where
    decSt Write = Empty
    decSt Read  = Full


transTermProc :: Defs -> Endom Term
transTermProc gdefs tm0
  | Proc cs proc0 <- reduceTerm' gdefs tm0
  = transProc (initEnv gdefs cs) proc0 (const $ Proc cs)
  | otherwise
  = tm0

transProgram :: Endom Program
transProgram = transProgramTerms transTermProc

reduceTerm' :: Defs -> Endom Term
reduceTerm' defs = pushDefs . reduceTerm . Scoped defs ø
-- -}
-- -}
-- -}
-- -}
