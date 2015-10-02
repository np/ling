module Ling.Proc
  ( actP
  , actPs
  , actsP
  , actsPs
  , prllActP
  , prllActPs
  , dotP
  , prllDotP
  , nxtP
  , prllNxtP
  , filter0s
  , filter0
  , suffChan
  , suffChans
  , split'
  , fwdP
  , fwdProc
  , ax
  , splitAx
  ) where

--import qualified Data.Set as Set
--import Data.Set (Set)
import Data.List

import Ling.Utils
import Ling.Norm
--import Ling.Subst (substi)
import Ling.Session

{-
type FreeChans a = a -> Set Channel

freeChans :: FreeChans Proc
freeChans (act `Act` procs) = fcAct act procs

bndChans :: FreeChans [ChanDec]
bndChans = l2s . map _argName

fcProcs :: FreeChans Procs
fcProcs = Set.unions . map freeChans

fcPref :: Act -> Endom (Set Channel)
fcPref act cs =
  case act of
    Nu c d         -> cs `Set.difference` bndChans [c,d]
    Split _ c ds   -> c  `Set.insert` (cs `Set.difference` bndChans ds)
    Send c _e      -> c  `Set.insert` cs
    Recv c _xt     -> c  `Set.insert` cs
    NewSlice{}     -> error "fcAct/NewSlice undefined"
    Ax _ ds        -> l2s ds `Set.union` cs
    At _ ds        -> l2s ds `Set.union` cs

fcAct :: Pref -> FreeChans Procs
fcAct act procs = foldr fcPref (fcProcs procs) pref
-}

infixr 4 `prllActP`

prllActP :: [Act] -> Procs -> Proc
[]   `prllActP` procs = mconcat procs
acts `prllActP` procs = acts `Act` procs

infixr 4 `prllActPs`

prllActPs :: [Act] -> Procs -> Procs
[]   `prllActPs` procs = procs
acts `prllActPs` procs = [acts `Act` procs]

infixr 4 `actP`

actP :: Act -> Procs -> Proc
act `actP` procs = [act] `Act` procs

infixr 4 `actsP`

actsP :: [Act] -> Procs -> Proc
[]       `actsP` procs = mconcat procs
act:acts `actsP` procs = act `actP` [acts `actsP` procs]

infixr 4 `actPs`

actPs :: Act -> Procs -> Procs
act `actPs` procs = [act `actP` procs]

infixr 4 `actsPs`

actsPs :: [Act] -> Procs -> Procs
[]   `actsPs` procs = procs
acts `actsPs` procs = [acts `actsP` procs]

infixr 4 `dotP`

dotP :: Proc -> Proc -> Proc
(pref0 `Act` procs0) `dotP` p1 = pref0 `Act` [procs0 `prllDotP` p1]

infixr 4 `prllDotP`

prllDotP :: Procs -> Proc -> Proc
prllDotP ps p = case ps of
  []   -> p
  [p0] -> p0 `dotP` p
  _    -> error "prllDotP: Cannot sequence parallel processes"

infixr 4 `nxtP`

nxtP :: Proc -> Proc -> Proc
(pref0 `Act` procs0) `nxtP` p1 = pref0 `Act` [procs0 `prllNxtP` p1]

infixr 4 `prllNxtP`

prllNxtP :: Procs -> Proc -> Proc
prllNxtP ps p = case ps of
  []   -> p
  [p0] -> p0 `nxtP` p
  _    -> error "prllNxtP: Cannot sequence parallel processes"

-- TODO: filtering 0-processes should not be necessary they should
-- not be part of the normal form.
filter0s :: Endom Procs
filter0s = concatMap filter0

filter0 :: Proc -> Procs
filter0 ([]   `Act` procs) = filter0s procs
filter0 (acts `Act` procs) = acts `prllActPs` filter0s procs

suffChan :: String -> Endom Channel
suffChan s = suffName $ s ++ "#"

suffChans :: (Show i, Integral i) => i -> Channel -> [Channel]
suffChans n c = map ((`suffChan` c) . show) [0..n-1]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

split' :: TraverseKind -> Channel -> [Channel] -> Act
split' k c = Split k c . map noSession

unRSession :: RSession -> Session
unRSession (Repl s (Lit (LInteger 1))) = s
unRSession _                           = error "unRSession"

-- One could generate the session annotations on the splits
fwdParTen :: [RSession] -> [Channel] -> Proc
fwdParTen _   []     = ø
fwdParTen rss (c:cs) = pref `actsP` ps
  -- These splits are independant, they are put in sequence because
  -- splitting always commutes anyway.
  where
    ss     = map unRSession rss
    n      = length ss
    ds:dss = map (suffChans n) (c:cs)
    ps     = zipWith fwdP ss (transpose (ds:dss))
    pref   = split' TenK c ds : zipWith (split' ParK) cs dss

fwdRcvSnd :: Typ -> Session -> [Channel] -> Proc
fwdRcvSnd _ _ []     = ø
fwdRcvSnd t s (c:cs) = pref `actsP` [fwdP s (c:cs)]
  where x    = prefName "x#" c
        vx   = Def x []
        pref = Recv c (Arg x t) : map (`Send` vx) cs

fwdDual :: Dual session
        => (session -> [channel] -> proc)
        ->  session -> [channel] -> proc
fwdDual f s (c:d:es) = f (dual s) (d:c:es)
fwdDual _ _ _        = error "fwdDual: Not enough channels for this forwarder (or the session is not a sink)"

fwdP :: Session -> [Channel] -> Proc
fwdP _  [] = ø
fwdP s0 cs =
  case s0 of
    Ten ss  ->         fwdParTen     ss cs
    Rcv t s ->         fwdRcvSnd t   s  cs
    Par ss  -> fwdDual fwdParTen     ss cs
    Snd t s -> fwdDual (fwdRcvSnd t) s  cs
    End     -> ø
    Atm{}   -> [ax s0 cs] `Act` []
    Seq _ss -> error "fwdP/Seq TODO"

-- The session 'Fwd n session' is a par.
-- This function builds a process which first splits this par.
fwdProc :: (Show i, Integral i) => i -> Session -> Channel -> Proc
fwdProc n s c = split' ParK c cs `actP` [fwdP s cs]
  where cs = suffChans n c

ax :: Session -> [Channel] -> Act
ax s cs | validAx s cs = Ax s cs
        | otherwise    = error "ax: Not enough channels given for this forwarder (or the session is not a sink)"

splitAx :: (Show i, Integral i) => i -> Session -> Channel -> [Act]
splitAx n s c = [split' ParK c cs, ax s cs]
  where cs = suffChans n c

{-
replProcs :: (Show i, Integral i) => i -> Name -> Procs -> Procs
replProcs n = concatMap . replProc n

replArg :: (Show i, Integral i) => i -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = map go [0..n-1] where
  go i = Arg (suffChan (show i) d) (substi (x, i) s)

replProc' :: Integral i => i -> Name -> Proc -> Procs
replProc' n x p = map go [0..n-1] where
  go i = substi (x, i) p

replPref :: (Show i, Integral i) => i -> Name -> Act -> Proc -> Proc
replPref n x pref p =
  case pref of
    Split k c [a]  -> [Split k c (replArg n x a)] `actP` replProc' n x p
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
replProc n x (pref0 `Act` procs) =
  case pref0 of
    []    -> replProcs n x procs
    [act] -> [replPref n x act procs]
  --  act : pref -> [replPref n x act (pref `actP` procs)]
-}
