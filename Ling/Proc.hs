{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeFamilies      #-}
module Ling.Proc
  ( Dottable(..)
  , _Pref
  , _PrefDotProc
  , _ActAt
  , __Act
  , _Chans
  , _SplitCs
  , _ArrayCs
  , _NewPatt
  , splitK
  , splitAx
  , subChanDecs
  , fetchActProc
  , procActs
  , procActsChans

  , fetchActPref -- Unused
  ) where

import Prelude hiding (pred)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Ling.Norm
import Ling.Print.Class
import Ling.Prelude
import Ling.Rename
import Ling.Session.Core (oneS, fwds)

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

instance Dottable Defs where
  defs0 `dotP` proc0
    | defs0 == ø = proc0
 -- | LetP defs1 proc1 <- proc0 = LetP (defs0 <> defs1) proc1
 -- ^ This is not necessary and causes bindings to be printed
 -- out of order.
    | otherwise = LetP defs0 proc0

instance Dottable Proc where
  proc0 `dotP` proc1
    | proc1 == ø = proc0
    | otherwise  =
      case proc0 of
        Act act -> act `dotP` proc1
        proc00 `Dot` proc01 -> proc00 `dotP` proc01 `dotP` proc1
        LetP defs proc00 -> defs `dotP` proc00 `dotP` proc1
        Replicate{} -> proc0 `Dot` proc1
        Procs procs0 -> procs0 `dotP` proc1
  toProc = id

-- Is a given process only a prefix?
_Pref :: Prism' Proc Pref
_Pref =  prism' toProc go
  where
    go = \case
      Act act            -> Just (Prll [act])
      Procs (Prll procs) -> post =<< mconcat <$> procs ^? below _Pref
      LetP{}             -> Nothing
      Dot{}              -> Nothing
      Replicate{}        -> Nothing
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

-- This prism matches only non-empty prefixes.
_PrefDotProc :: Prism' Proc (Pref, Proc)
_PrefDotProc = prism' (uncurry dotP) go
  where
    go = \case
      Act act -> Just (Prll [act], ø)
      proc0 `Dot` proc1 -> proc0 ^? _Pref . to (\pref -> (pref, proc1))
      Procs{} -> Nothing
      LetP{} -> Nothing
      Replicate{} -> Nothing

cPattAsArrayChanDecs :: CPatt -> Maybe (TraverseKind, [ChanDec])
cPattAsArrayChanDecs = \case
  ChanP cd -> Just (ParK, [cd])
  ArrayP k patts -> patts ^? below _ChanP . to ((,) k)

{- Not used yet...
matchCPatt :: CPatt -> CPatt -> Maybe [(ChanDec,ChanDec)]
matchCPatt p0 p1 =
  case (p0, p1) of
    (ArrayP k0 ps0, ArrayP k1 ps1)
       | k0 == k1  -> matchCPatts ps0 ps1
       | otherwise -> Nothing
    (ChanP cd0, ChanP cd1) -> Just [(cd0, cd1)]
    _ -> Nothing
-}

-- This is incomplete as some valid processes can be missed.
-- TODO generate a `cut` when this short-cut does not work.
matchProcSplit :: TraverseKind -> Endom Proc -> ChanDec -> Proc -> Maybe (Endom Proc, [ChanDec], Proc)
matchProcSplit k pref cd = \case
  proc0 `Dot` proc1 ->
    -- trace ("matchProcSplit: Dot " <> show proc0) $
    case proc0 of
      Act (Split c pat)
        | c == cd ^. cdChan
        , Just (k', cds) <- cPattAsArrayChanDecs pat
        , k == k'
        -> Just (pref, cds, proc1)
      _ -> matchProcSplit k (pref . dotP proc0) cd proc1
  Act act ->
    matchProcSplit k pref cd (Act act `Dot` ø)
  LetP defs proc0 ->
    matchProcSplit k (pref . dotP defs) cd proc0
  -- proc0 -> trace ("matchProcSplit: " <> show proc0) Nothing
  _ -> Nothing

matchChanDecs :: TraverseKind -> EndoM Maybe (Endom Proc, [ChanDec], Proc)
matchChanDecs k = \case
  (pref,[cd],proc) -> matchProcSplit k pref cd proc
  _                -> Nothing

-- Prism valid up to the reduction rules
_ActAt :: Prism' Proc (Term, CPatt)
_ActAt = prism con pat
  where
    con (t, p) =
      -- (\proc0 -> trace ("_ActAt (" ++ ppShow t ++ ", " ++ ppShow p ++ ") = " ++ ppShow proc0) proc0) $
      case t of
        Proc cs0 proc0 ->
          case cPattAsArrayChanDecs p of
            Just (k, cs') | Just (pref1, cs1, proc1) <- matchChanDecs k (id, cs0, proc0)
                          , length cs1 == length cs' -> pref1 $ renProc (zip cs1 cs') proc1
                          | k == ParK
                          , length cs0 == length cs' -> renProc (zip cs0 cs') proc0
            _ -> p0
        _ -> p0
      where
        p0 = Act (At t p)

    pat (Act (At t p)) = Right (t, p)
    pat proc0          = Left  proc0

    renProc bs = renameI r
      where
        l = bs & each . both %~ view cdChan
        m = l2m l
        r = Ren (\_ _ x -> pure $ Map.lookup x m ?| x) ø ø

-- Prism valid up to the reduction rules
__Act :: Prism' Proc Act
__Act = prism con pat
  where
    con act = Act act & _ActAt %~ id
    pat (Act act) = Right act
    pat proc0     = Left proc0

_Chans :: Prism' [CPatt] [ChanDec]
_Chans = below _ChanP

_ArrayCs :: Prism' CPatt (TraverseKind, [ChanDec])
_ArrayCs = _ArrayP . aside _Chans

_NewPatt :: Prism' CPatt NewPatt
_NewPatt = prism' con pat
  where
    con = \case
      NewChan c ty -> ChanP (ChanDec c (litR1 # ()) (Just . oneS $ IO Write (Arg anonName (Just ty)) (Array SeqK (Sessions []))))
      NewChans k cds -> ArrayP k (ChanP <$> cds)
    pat = \case
      ChanP (ChanDec c r os) | r & is litR1 ->
        case os of
          Just (IO Write (Arg x (Just ty)) (Array SeqK (Sessions [])) `Repl` r') | x == anonName, r' & is litR1 ->
            Just (NewChan c ty)
          _ ->
            Nothing
      ArrayP k pats | Just cds <- pats ^? _Chans ->
        Just (NewChans k cds)
      _ ->
        Nothing

_SplitCs :: Prism' Act (Channel, TraverseKind, [ChanDec])
_SplitCs = _Split . aside _ArrayCs . flat3

splitK :: TraverseKind -> Channel -> [ChanDec] -> Act
splitK k c cs = _SplitCs # (c, k, cs)

splitAx :: Int -> Session -> Channel -> [Act]
splitAx n s c = [splitK ParK c cs, Ax s (_cdChan <$> cs)]
  where
    ss = oneS <$> fwds n s
    cs = subChanDecs ss c

subChanDecs :: [RSession] -> Channel -> [ChanDec]
subChanDecs rss c = [ ChanDec c' (rs ^. rfactor) (Just rs)
                    | (i, rs) <- zip [0 :: Int ..] rss
                    , let c' = suffixedChan (show i) # c ]

procActs :: Traversal' Proc Act
procActs f = \case
  Act act -> Act <$> f act
  Procs procs -> Procs <$> (each . procActs) f procs
  Replicate k t x proc0 ->
    mkReplicate k t x <$> procActs f proc0
  proc0 `Dot` proc1 ->
    Dot <$> procActs f proc0 <*> procActs f proc1
  LetP defs proc0 -> LetP defs <$> procActs f proc0

-- Only a traversal if we don't put back actions about these channels
-- NOTE: not used
procActsChans :: Print Act => Set Channel -> Traversal' Proc Act
procActsChans cs = procActs . filtered (not . Set.null . chanSetOf)
  where
    chanSetOf act = fcActSetCheck act `Set.intersection` cs

{-
skippableAct :: Channel -> Act -> Bool
skippableAct c = \case
  Send{}     -> False
  Recv{}     -> False
  Replicate{}-> False -- TODO
  Ax{}       -> False -- TODO
  At{}       -> False -- TODO

  LetA{} -> True
  Split _ _ cds
    | c `notElem` (cds ^.. each . argName) ->
        True
    | otherwise ->
        error $ "skippableAct: re-used channel names " ++ show (c, cds)
  Nu ds
    | c `notElem` ds ^.. each . argName ->
        True
    | otherwise ->
        error $ "skippableAct: re-used channel names " ++ show (c, ds)

skippableActs :: Channel -> [Act] -> Bool
skippableActs c acts = null acts || all (skippableAct c) acts
-}

fetchActAct :: Print Act => (Set Channel -> Bool) -> Lens Act Proc (Maybe Act) Proc
fetchActAct pred f act
  | pred (fcActSetCheck act) = f (Just act)
  | otherwise                  = (act `dotP`) <$> f Nothing

fetchActPref :: Print Act => (Set Channel -> Bool) -> Lens [Act] Proc (Maybe Act) Proc
fetchActPref pred f = \case
  [] -> f Nothing
  (act:acts)
    | pred (fcActSetCheck act) -> (Prll acts `dotP`) <$> f (Just act)
    | otherwise                -> (act  `dotP`)      <$> fetchActPref pred f acts

fcProcSetCheck :: Print Proc => Proc -> Set Channel
fcProcSetCheck = setOf freeChans

fcActSetCheck :: Print Act => Act -> Set Channel
fcActSetCheck = setOf freeChans

fetchActProcs :: (Print Act, Print Proc) => (Set Channel -> Bool) -> Lens Procs Procs (Maybe Act) Proc
fetchActProcs pred = _Prll . go
  where
    go f = \case
      [] -> pure <$> f Nothing
      proc0:procs
        | pred (fcProcSetCheck proc0) -> (:procs) <$> fetchActProc' pred f proc0
        | otherwise                   -> (proc0:) <$> go                 f procs

fetchActProc :: (Print Act, Print Proc) => (Set Channel -> Bool) -> Lens' Proc Proc
fetchActProc pred f proc = fetchActProc' pred (f . toProc) proc

fetchActProc' :: (Print Act, Print Proc) => (Set Channel -> Bool) -> Lens Proc Proc (Maybe Act) Proc
fetchActProc' pred f = \case
  Act act -> fetchActAct pred f act
  Procs procs -> toProc <$> fetchActProcs pred f procs
  Replicate k t x proc0 ->
    mkReplicate k t x <$> fetchActProc' pred f proc0
  LetP defs proc0 ->
    LetP defs <$> fetchActProc' pred f proc0
  proc0 `Dot` proc1
    | pred (fcProcSetCheck proc0) -> (`dotP` proc1) <$> fetchActProc' pred f proc0
    | otherwise                   -> (proc0 `dotP`) <$> fetchActProc' pred f proc1

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
    Replicate{}    -> error "replPref/Replicate"
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
