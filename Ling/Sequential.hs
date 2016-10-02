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
import Ling.Reduce (flatRSessions, reduce, reduced)
import Ling.Scoped (Scoped(Scoped), scoped, ldefs, allDefs)
import Ling.Subst (substScoped)
import Ling.SubTerms (transProgramTerms)
import Ling.Defs (mkLetS)

data Status = Full | Empty deriving (Eq,Read,Show)

rwStatus :: RW -> Status
rwStatus = \case
  Write -> Empty
  Read  -> Full

status :: Iso' (Maybe ()) Status
status = iso toStatus fromStatus
  where
    toStatus Nothing    = Empty
    toStatus (Just  ()) = Full
    fromStatus Empty = Nothing
    fromStatus Full  = Just ()

-- One could add a External
data LocationKind
  = Unique
  | Normal
  deriving (Read,Show,Ord,Eq)

data Location
  = Root { _rootKind :: LocationKind, _rootChannel :: Channel }
  | Proj Location Int
  | Next Location
  deriving (Read,Show,Ord,Eq)

$(makeLenses ''Location)

proj :: Location -> Int -> Location
proj l i | Root Unique _ <- l = l
         | otherwise          = Proj l i

next :: Endom Location
next l | Root Unique _ <- l = l
       | otherwise          = Next l

data Env = Env { _chans   :: Map Channel Location
               , _edefs   :: Defs
               -- ^ This stores only definitions which are put back into the
               -- output.
               -- Top level definitions and process level definitions are
               -- added here, while term level definitions are pushed around
               -- using reduction.
               -- Thus all definitions part of edefs are global definitions for Scoped.
               , _locs    :: Map Location ()
               , _writers :: Map Location Channel
               -- writers ^. at l == Just c
               -- means that the process owning c was the
               -- last one to write at location l.
               , _gas     :: Int
               -- ^ Do not spend more than `gas` steps.
               }
  deriving (Show)

$(makeLenses ''Env)

scope :: Getter Env (Scoped ())
scope = to $ \env -> Scoped (env ^. edefs) ø ()

transErr :: Print a => String -> a -> b
transErr msg v = error $ msg ++ "\n" ++ pretty v

emptyEnv :: Env
emptyEnv = Env ø ø ø ø maxBound

addChans :: [(Channel, Location)] -> Endom Env
addChans = over chans . Map.union . l2m

rmChan :: Channel -> Endom Env
rmChan c = chans .\\ c

(!) :: Env -> Channel -> Location
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

stepEnv :: Channel -> RW -> Endom Env
stepEnv c _rw env =
  env & chans   . at c . mapped %~ next
      & locs    . at l %~ mnot ()
      & writers . at l %~ mnot c
      -- TODO: why do we toggle the writer even we are only reading?
  where l = env ! c

splitLoc :: Location -> [ChanDec] -> [(Channel, Location)]
splitLoc l dOSs = [ (d, proj l n) | (d, n) <- zip ds [0 :: Int ..] ]
  where
    ds = dOSs ^.. each . cdChan

sessionsStatus :: (RW -> Status) -> Location -> Scoped Sessions -> [(Location,Status)]
sessionsStatus dflt l sss =
  [ ls
  | (i,ss) <- zip [0..] $ flatRSessions sss
  , ls <- rsessionStatus dflt (proj l i) (sss *> ss) ]

sessionStatus :: (RW -> Status) -> Location -> Scoped Session -> [(Location,Status)]
sessionStatus dflt l ss =
  case ss ^. scoped of
    Array _ sessions -> sessionsStatus dflt l (ss $> sessions)
    IO rw _ s  -> (l, dflt rw) : sessionStatus dflt (next l) (ss $> s)
    TermS p t ->
      let st' = reduce (ss $> t) ^. reduced in
      case st' ^. scoped of
        TSession s -> sessionStatus dflt l (ss *> st' $> sessionOp p s)
        _          -> trace ("[WARNING] Skipping abstract session " ++ pretty (substScoped (ss *> st')))
                      [(l, Empty)]

rsessionStatus :: (RW -> Status) -> Location -> Scoped RSession -> [(Location,Status)]
rsessionStatus dflt l ssr@(Scoped _ _ sr)
  | Just s <- sr ^? _OneS = sessionStatus  dflt l (ssr $> s)
  | otherwise             = sessionsStatus dflt l (ssr $> Sessions [sr])

isReadyFor :: Channel -> RW -> Env -> Bool
isReadyFor c rw env
  =  (l ^? rootKind == Just Unique)
  || (Just c /= d -- We were the last one to write so we're not ready
      && s == rwStatus rw)
  where
    l = env ! c
    s = env ^. locs . at l . status
    d = env ^. writers . at l

-- TODO generalize by looking deeper at what is ready now
splitReady :: Env -> Pref -> (Pref, Pref)
splitReady env = bimap Prll Prll . partition (isReady env) . _unPrll

isReady :: Env -> Act -> Bool
isReady env = \case
  Split{}    -> True
  Nu{}       -> True
  Ax{}       -> True
  -- `At` is considered non-ready. Therefor we cannot put
  -- a process like (@p0() | @p1()) in sequence.
  At{}       -> False
  Send c _ _ -> isReadyFor c Write env
  Recv c _   -> isReadyFor c Read  env

-- TODO: Scoped CPatt ?
transSplitPatt :: Channel -> CPatt -> Endom Env
transSplitPatt c pat env =
  case pat ^? _ArrayCs of
    Just (_, cs) -> transSplit c cs env
    Nothing -> error "Sequential.transSplitPatt: unsupported pattern"

-- TODO: Scoped [ChanDec]
transSplit :: Channel -> [ChanDec] -> Endom Env
transSplit c dOSs env = rmChan c $ addChans (splitLoc (env ! c) dOSs) env

-- All these prefixes can be reordered as they are in parallel
transPref :: Env -> Pref -> (Env -> Proc -> r) -> r
transPref env (Prll pref0) k =
  case pref0 of
    []       -> k (env & gas -~ 1) ø
    act:pref ->
      transPref (transAct (env ^. scope $> act) env) (Prll pref) $ \env' proc' ->
        k env' (act `dotP` proc')


addChanDecs :: LocationKind -> Scoped [Arg Session] -> Endom Env
addChanDecs lk scds =
  case scds ^. scoped of
    [] -> id
    cds@(Arg c0 c0S : _) ->
      let l = Root lk c0 in
      addLocs  (sessionStatus (const Empty) l (scds $> c0S)) .
      addChans [(c,l) | Arg c _ <- cds]

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

transNew :: Scoped NewPatt -> Endom Env
transNew spat =
  case spat ^. scoped of
    NewChans _ [] ->
      id
    NewChans _ cds0 ->
      addChanDecs Normal . (spat $>)
            $ [ Arg c cOS | ChanDec c _ cOS <- cds0 ]
            & each . argBody . _Just %~ unsafeUnRepl
            & unsafePartsOf (each . argBody) %~ extractDuals
    NewChan c ty ->
      addChanDecs Unique $ spat $> [Arg c (sendS ty (endS # ()))]

transAct :: Scoped Act -> Endom Env
transAct sact =
  case sact ^. scoped of
    Nu _ cpatt   -> transNew $ sact $> cpatt ^?! _NewPatt
    Split c pat  -> transSplitPatt c pat
    Send c _ _   -> stepEnv c Write
    Recv c _     -> stepEnv c Read
    Ax{}         -> id
    At{}         -> id

transProc :: Env -> Proc -> (Env -> Proc -> r) -> r
transProc env proc0 = transProcs env [proc0] []

transProcs :: Env -> [Proc] -> [Proc] -> (Env -> Proc -> r) -> r
transProcs env0 p0s waiting k0
  | env0 ^. gas <= 0 = k0 env0 (Procs (Prll (p0s ++ waiting)))
  | otherwise =
  case p0s of
    [] ->
      case waiting of
        []     -> k0 env0 ø
        [p]    -> transProcs env0 [p] [] k0
        _   -> transErr "All the processes are stuck" waiting

    p0':ps ->
      let rp0 = reduce (env0 ^. scope $> p0') ^. reduced
          env1 = env0 & edefs <>~ rp0 ^. ldefs
          k1 env2 p2 = k0 env2 (rp0 ^. ldefs `dotP` p2)
          p0 = rp0 ^. scoped
          transProcsProgress env proc0 procs =
            transProcs env (ps ++ reverse waiting ++ procs) [] $ \env2 procs' ->
              k1 env2 (proc0 `dotP` procs')
          transDelay = transProcs env1 ps (p0 : waiting) k1
      in
      case p0 of
        Replicate _ t x p ->
          transProc env1 p $ \env2 p' ->
            transProcsProgress env2 (mkReplicate SeqK t x p') []

        Procs (Prll ps0) ->
          transProcs env1 (ps0 ++ ps) waiting k1

        -- This is a short-cut case this means that it should work the same without it.
        Act act | isReady env1 act ->
          transProcsProgress (transAct (env1 ^. scope $> act) env1) (Act act) []

        -- Short-cut case, same as above.
        Act act `Dot` proc1 | isReady env1 act ->
          transProcsProgress (transAct (env1 ^. scope $> act) env1) (Act act) [proc1]

        _ | Just (pref, p1) <- p0 ^? _PrefDotProc ->
            case () of
            _ | pref == ø -> transErr "transProcs: pref == ø IMPOSSIBLE" p0
            _ | (readyPis@(Prll(_:_)),restPis) <- splitReady env1 pref ->
              transPref env1 readyPis $ \env2 proc' ->
                transProcsProgress env2 proc' [restPis `dotP` p1]

            _ | null ps ->
              trace ("[WARNING] Sequencing a non-ready prefix " ++ pretty pref) $
              transPref env1 pref $ \env2 proc' ->
                transProcsProgress env2 proc' [p1]

            _ -> transDelay

        LetP defs0 proc0 ->
          transProcsProgress (env1 & edefs <>~ defs0) defs0 [proc0]

        proc0 `Dot` proc1
          | null ps ->
              (if proc0 & is _Replicate then id else
                trace ("[WARNING] Sequencing process `" ++ pretty proc0 ++ "`")) $
              transProc env1 proc0 $ \env2 proc0' ->
                transProcsProgress env2 proc0' [proc1]
          | otherwise ->
              transDelay

        _ -> error "IMPOSSIBLE: transProcs"

initEnv :: Int -> Scoped () -> [ChanDec] -> Env
initEnv maxgas sc cs =
  emptyEnv
    & edefs .~ allDefs sc
    & gas .~ maxgas
    & addLocs  [ ls | ChanDec c _ (Just s) <- cs
               , ls <- rsessionStatus rwStatus (Root Normal c) (sc $> s) ]
    & addChans [ (c, Root Normal c) | ChanDec c _ _ <- cs ]


transTermProc :: Int -> Defs -> Endom Term
transTermProc maxgas gdefs tm0
  | tm1 <- reduce (Scoped gdefs ø tm0) ^. reduced
  , Proc cs proc0 <- tm1 ^. scoped
  = transProc (initEnv maxgas (Scoped gdefs (tm1 ^. ldefs) ()) cs) proc0 . const $
      mkLetS . (tm1 $>) . Proc cs
  | otherwise
  = tm0

transProgram :: Int -> Defs -> Endom Program
transProgram maxgas pdefs = transProgramTerms $ transTermProc maxgas . (pdefs <>)
-- -}
-- -}
-- -}
-- -}
