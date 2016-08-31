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
import Ling.Defs (mkLet, mkLet__, mkLetS)

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

stepEnv :: Channel -> Term -> Endom Env
stepEnv c tm env =
  env & chans   . at c . mapped %~ bimap Next (rsession %~ sessionStep tm)
      & locs    . at l %~ mnot ()
      & writers . at l %~ mnot c
  where l = fst (env!c)

sessionsStatus :: (RW -> Status) -> Location -> Scoped Sessions -> [(Location,Status)]
sessionsStatus dflt l sss =
  [ ls
  | (i,ss) <- zip [0..] $ flatRSessions sss
  , ls <- rsessionStatus dflt (Proj l i) (sss *> ss) ]

sessionStatus :: (RW -> Status) -> Location -> Scoped Session -> [(Location,Status)]
sessionStatus dflt l ss =
  case ss ^. scoped of
    Array _ sessions -> sessionsStatus dflt l (ss $> sessions)
    IO rw _ s  -> (l, dflt rw) : sessionStatus dflt (Next l) (ss $> s)
    TermS p t ->
      let st' = reduce (ss $> t) ^. reduced in
      case st' ^. scoped of
        TSession s -> sessionStatus dflt l (ss *> st' $> sessionOp p s)
        _          -> trace ("[WARNING] Skipping abstract session " ++ pretty (substScoped (ss *> st')))
                      [(l, Empty)]

rsessionStatus :: (RW -> Status) -> Location -> Scoped RSession -> [(Location,Status)]
rsessionStatus dflt l ssr@(Scoped _ _ sr@(s `Repl` r))
  | litR1 `is` r = sessionStatus  dflt l (ssr $> s)
  | otherwise    = sessionsStatus dflt l (ssr $> Sessions [sr])

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

isReady :: Env -> Act -> Bool
isReady env = \case
  Split{}    -> True
  Nu{}       -> True
  Ax{}       -> True
  -- `At` is considered non-ready. Therefor we cannot put
  -- a process like (@p0() | @p1()) in sequence.
  At{}       -> False
  Send c _ _ -> statusAt c env == Just Empty
  Recv c _   -> statusAt c env == Just Full

-- TODO: Scoped CPatt ?
transSplitPatt :: Channel -> CPatt -> Endom Env
transSplitPatt c pat env =
  case pat ^? _ArrayCs of
    Just (_, cs) -> transSplit c cs env
    Nothing -> error "Sequential.transSplitPatt: unsupported pattern"

-- TODO: Scoped [ChanDec]
transSplit :: Channel -> [ChanDec] -> Endom Env
transSplit c dOSs env =
  rmChan c $
  addChans [ (d, (Proj l n, oneS (projSessions (integral # n) sessions)))
           | (d, n) <- zip ds [(0 :: Int)..] ] env
  where (l, session) = env ! c
        sessions = session ^? to unRepl . _Array . _2 {-. to unsafeFlatSessions-} ?| error "transSplit: expected to split an array"
        ds = dOSs ^.. each . cdChan

-- All these prefixes can be reordered as they are in parallel
transPref :: Env -> Pref -> (Env -> Proc -> r) -> r
transPref env (Prll pref0) k =
  case pref0 of
    []       -> k (env & gas -~ 1) ø
    act:pref ->
      transPref (transAct (env ^. scope $> act) env) (Prll pref) $ \env' proc' ->
        k env' (act `dotP` proc')


addChanDecs :: Scoped [Arg Session] -> Endom Env
addChanDecs scds =
  case scds ^. scoped of
    [] -> id
    cds@(Arg c0 c0S : _) ->
      let l = Root c0 in
      addLocs  (sessionStatus (const Empty) l (scds $> c0S)) .
      addChans [(c,(l,oneS (mkLet__ (scds $> cS)))) | Arg c cS <- cds]

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
      addChanDecs . (spat $>)
            $ [ Arg c cOS | ChanDec c _ cOS <- cds0 ]
            & each . argBody . _Just %~ unRepl
            & unsafePartsOf (each . argBody) %~ extractDuals
    NewChan _ Nothing -> error "transNew: TODO"
    NewChan c (Just ty) ->
      addChanDecs $ spat $> [Arg c (sendS ty (endS # ()))]

transAct :: Scoped Act -> Endom Env
transAct sact =
  case sact ^. scoped of
    Nu _ newpatt -> transNew $ sact $> newpatt
    Split c pat  -> transSplitPatt c pat
    Send c _ t   -> stepEnv c $ mkLet (sact ^. ldefs) t
    Recv c a     -> stepEnv c $ mkVar (a ^. argName)
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
      in
      case p0 of
        NewSlice cs t x p ->
          transProc env1 p $ \env2 p' ->
            transProcsProgress env2 (NewSlice cs t x p') []

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

            _ ->
              transProcs env1 ps (p0 : waiting) k1

        LetP defs0 proc0 ->
          transProc (env1 & edefs <>~ defs0) proc0 $ \env2 proc0' ->
            k1 env2 (defs0 `dotP` proc0')

        proc0 `Dot` proc1 ->
          transProc env1 proc0 $ \env2 proc0' ->
            transProc env2 proc1 $ \env3 proc1' ->
              k1 env3 (proc0' `dotP` proc1')

        _ -> error "IMPOSSIBLE: transProcs"

initEnv :: Int -> Scoped () -> [ChanDec] -> Env
initEnv maxgas sc cs =
  emptyEnv
    & edefs .~ allDefs sc
    & gas .~ maxgas
    & addLocs  [ ls | ChanDec c _ (Just s) <- cs
               , ls <- rsessionStatus decSt (Root c) (sc $> s) ]
    & addChans [ (c, (Root c, s)) | ChanDec c _ (Just s) <- cs ]
  where
    decSt Write = Empty
    decSt Read  = Full


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
