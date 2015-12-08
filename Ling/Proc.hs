{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeFamilies      #-}
module Ling.Proc
  ( Dottable(..)
  , _Pref
  , _PrefDotProc
  , split'
  , fwdP
  , fwdProc
  , ax
  , splitAx

  -- All functions below are currently unused.
  , fetchActProc
  , fetchActPref
  , procActs
  , procActsChans
  ) where

import Prelude hiding (pred)
import qualified Data.Set as Set
import Ling.Free (fcAct,fcProc)
import Ling.Norm
import Ling.Prelude
import Ling.Session

infixr 4 `dotP`
infixr 4 `dotPs`

class Dottable proc where
  dotP  :: proc -> Endom Proc

  dotPs :: proc -> Endom Procs
  dotPs proc = asProcs . dotP proc . mconcat . _unPrll
    where
      asProcs (Procs procs) = procs
      asProcs p             = Prll [p]

  dotsP :: [proc] -> Proc
  dotsP = foldr dotP ø

  dotsPs :: [proc] -> Procs
  dotsPs = foldr dotPs ø

  toProc :: proc -> Proc
  toProc = (`dotP` ø)

  toProcs :: proc -> Procs
  toProcs = (`dotPs` ø)

-- Not exported: used internally only
dotQ :: Op2 Proc
dotQ proc0 proc1
  | proc1 == ø = proc0
  | otherwise  = proc0 `Dot` proc1

instance Dottable a => Dottable (Maybe a) where
  Nothing `dotP` proc = proc
  Just a  `dotP` proc = a `dotP` proc

instance Dottable act => Dottable (Order act) where
  Order []         `dotP` proc = proc
  Order (act:acts) `dotP` proc = act `dotP` Order acts `dotP` proc

instance Dottable Act where
  act `dotP` proc = Act act `dotQ` proc
  toProc = Act

instance Dottable Proc where
  proc0 `dotP` proc1
    | proc1 == ø = proc0
    | otherwise  =
      case proc0 of
        Act act -> act `dotP` proc1
        proc00 `Dot` proc01 -> proc00 `dotP` proc01 `dotP` proc1
        NewSlice{} -> proc0 `Dot` proc1
        Procs procs0 -> procs0 `dotP` proc1
  toProc = id

-- Is a given process only a prefix?
_Pref :: Prism' Proc Pref
_Pref =  prism' toProc go
  where
    go = \case
      Act act            -> Just (Prll [act])
      Procs (Prll procs) -> post =<< mconcat <$> procs ^? below _Pref
      Dot{}              -> Nothing
      NewSlice{}         -> Nothing
    post pref@(Prll acts) =
      case acts of
        [_] -> Just pref
        _ | all isSendRecv acts -> Just pref
        _                       -> Nothing

instance Dottable proc => Dottable (Prll proc) where
  Prll procs0 `dotP` proc1
    | [] <- procs0 = proc1
    | [proc0] <- procs0 = proc0 `dotP` proc1
    | proc1 == ø = Procs (Prll procs0')
    | Just pref <- procs0' ^? below _Pref = mconcat pref `pdotP` proc1
    | otherwise =
        error . unlines $
          ["Unsupported sequencing of parallel processes"
          ,show procs0'
          ,show proc1
          ]

    where
      procs0' = toProc <$> procs0

      Prll []    `pdotP` proc = proc
      Prll [act] `pdotP` proc = act `dotP` proc
      Prll acts  `pdotP` proc = Procs (Prll (Act <$> acts)) `dotQ` proc

_PrefDotProc :: Prism' Proc (Pref, Proc)
_PrefDotProc = prism' (uncurry dotP) go
  where
    go = \case
      Act act -> Just (Prll [act], ø)
      procs@Procs{} -> Just (ø, procs)
      proc0 `Dot` proc1 -> proc0 ^? _Pref . to (\pref -> (pref, proc1))
      NewSlice{} -> Nothing

subChans :: (Show i, Integral i) => i -> Channel -> [Channel]
subChans n c = [ suffixedChan (show i) # c | i <- [0..n-1] ]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

split' :: TraverseKind -> Channel -> [Channel] -> Act
split' k c = Split k c . map noSession

unRSession :: RSession -> Session
unRSession (s `Repl` r)
  | litR1 `is` r = s
  | otherwise    = error "unRSession"

type MkFwd a = (Session -> Session) -> UsedNames -> a -> [Channel] -> Proc

-- One could generate the session annotations on the splits
fwdSplit :: [TraverseKind] -> ([Proc] -> Proc) -> MkFwd [RSession]
fwdSplit ks fprocs redSession used rss cs
  | null cs   = ø
  | otherwise = Order pref `dotP` fprocs ps
  -- These splits are independant, they are put in sequence because
  -- splitting always commutes anyway.
  where
    ss   = unRSession <$> rss
    dss  = subChans (length ss) <$> cs
    ps   = zipWith     (fwdP redSession used) ss (transpose dss)
    pref = zipWith3 id (split' <$> ks) cs dss

fwdParTen, fwdSeqSeq :: MkFwd [RSession]
fwdParTen = fwdSplit (TenK : repeat ParK) mconcat
fwdSeqSeq = fwdSplit (repeat SeqK)        dotsP

fwdIO :: MkFwd (RW, VarDec, Session)
fwdIO _          _    _               []     = ø
fwdIO redSession used (Write, arg, s) ds     = fwdDual fwdP redSession used (IO Write arg s) ds
fwdIO redSession used (Read,  arg, s) (c:ds) = recv `dotP` Prll sends `dotP` fwdP redSession used' s (c:ds)
  where (x, used') = avoidUsed (arg^.argName) c used
        vx         = Def x []
        recv       = Recv c (arg & argName .~ x)
        sends      = [ Send d vx | d <- ds ]

fwdDual :: Dual session
        => (redsession -> usednames -> session -> [channel] -> proc)
        ->  redsession -> usednames -> session -> [channel] -> proc
fwdDual f r u s (c:d:es) = f r u (dual s) (d:c:es)
fwdDual _ _ _ _ _        = error "fwdDual: Not enough channels for this forwarder (or the session is not a sink)"

fwdArray :: TraverseKind -> MkFwd [RSession]
fwdArray k = case k of
  SeqK -> fwdSeqSeq
  TenK -> fwdParTen
  ParK -> fwdDual fwdParTen

fwdP :: MkFwd Session
fwdP _          _    _  [] = ø
fwdP redSession used s0 cs
  | endS `is` s0 = ø
  | otherwise    =
  case redSession s0 of
    Array k ss -> fwdArray k redSession used ss cs
    IO p t s   -> fwdIO redSession used (p, t, s) cs
    TermS{}    -> Act $ ax s0 cs

-- The session 'Fwd n session' is a par.
-- This function builds a process which first splits this par.
fwdProc :: (Show i, Integral i) => i -> Session -> Channel -> Proc
fwdProc n s c = split' ParK c cs `dotP` fwdP id ø s cs
  where cs = subChans n c

ax :: Session -> [Channel] -> Act
ax s cs | validAx s cs = Ax s cs
        | otherwise    = error "ax: Not enough channels given for this forwarder (or the session is not a sink)"

splitAx :: (Show i, Integral i) => i -> Session -> Channel -> [Act]
splitAx n s c = [split' ParK c cs, ax s cs]
  where cs = subChans n c

procActs :: Traversal' Proc Act
procActs f = \case
  Act act -> Act <$> f act
  Procs procs -> Procs <$> (each . procActs) f procs
  NewSlice cs t x proc0 ->
    NewSlice cs t x <$> procActs f proc0
  proc0 `Dot` proc1 ->
    Dot <$> procActs f proc0 <*> procActs f proc1

-- Only a traversal if we don't put back actions about these channels
procActsChans :: Set Channel -> Traversal' Proc Act
procActsChans cs = procActs . filtered (\act -> not (Set.null (fcAct act `Set.intersection` cs)))

fetchActAct :: (Set Channel -> Bool) -> Lens Act Proc (Maybe Act) Proc
fetchActAct pred f act
  | pred (fcAct act) = f (Just act)
  | otherwise        = (act `dotP`) <$> f Nothing

fetchActPref :: (Set Channel -> Bool) -> Lens [Act] Proc (Maybe Act) Proc
fetchActPref pred f = \case
  [] -> f Nothing
  (act:acts)
    | pred (fcAct act) -> (Prll acts `dotP`) <$> f (Just act)
    | otherwise        -> (act  `dotP`)      <$> fetchActPref pred f acts

fetchActProcs :: (Set Channel -> Bool) -> Lens Procs Procs (Maybe Act) Proc
fetchActProcs pred = _Prll . go
  where
    go f = \case
      [] -> pure <$> f Nothing
      proc0:procs
        | pred (fcProc proc0) -> (:procs) <$> fetchActProc' pred f proc0
        | otherwise           -> (proc0:) <$> go                 f procs

fetchActProc :: (Set Channel -> Bool) -> Lens' Proc Proc
fetchActProc pred f proc = fetchActProc' pred (f . toProc) proc

fetchActProc' :: (Set Channel -> Bool) -> Lens Proc Proc (Maybe Act) Proc
fetchActProc' pred f = \case
  Act act -> fetchActAct pred f act
  Procs procs -> toProc <$> fetchActProcs pred f procs
  NewSlice cs t x proc0 ->
    NewSlice cs t x <$> fetchActProc' pred f proc0
  proc0 `Dot` proc1
    | pred (fcProc proc0) -> (`dotP` proc1) <$> fetchActProc' pred f proc0
    | otherwise           -> (proc0 `dotP`) <$> fetchActProc' pred f proc1

{-
replProcs :: (Show i, Integral i) => i -> Name -> Endom Procs
replProcs n = concatMap . replProc n

replArg :: (Show i, Integral i) => i -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = go <$> [0..n-1] where
  go i = Arg (suffChan (show i ++ "#") d) (substi (x, i) s)

replProc' :: Integral i => i -> Name -> Proc -> Procs
replProc' n x p = go <$> [0..n-1] where
  go i = substi (x, i) p

replPref :: (Show i, Integral i) => i -> Name -> Act -> Endom Proc
replPref n x pref p =
  case pref of
    Split k c [a]  -> [Split k c (replArg n x a)] `dotP` replProc' n x p
    Split{}        -> error "replPref/Split"
    Send _c _e     -> error "replPref/Send"
    Recv _c _xt    -> error "replPref/Recv"
    Nu _c _d       -> error "replPref/Nu"
    NewSlice{}     -> error "replPref/NewSlice"
    -- If Ax are expanded before, nothing to do here
    -- Otherwise this should do the same as the
    -- replication of the expansion.
    -- This might be needed because of abstract sessions.
    Ax{}           -> error "replProc/Ax"
    At{}           -> error "replProc/At"

replProc :: (Show i, Integral i) => i -> Name -> Proc -> Procs
replProc n x (pref0 `Dot` procs) =
  case pref0 of
    []    -> replProcs n x procs
    [act] -> [replPref n x act procs]
  --  act : pref -> [replPref n x act (pref `dotP` procs)]
-}
-- -}
