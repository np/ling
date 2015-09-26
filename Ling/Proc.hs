module Ling.Proc where

import Ling.Abs (Name)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List

import Ling.Utils
import Ling.Norm
import Ling.Subst (substi)
import Ling.Session

type FreeChans a = a -> Set Channel

freeChans :: FreeChans Proc
freeChans (prefs `Act` procs) = fcAct prefs procs

bndChans :: FreeChans [ChanDec]
bndChans = l2s . map _argName

fcProcs :: FreeChans Procs
fcProcs = Set.unions . map freeChans

fcAct :: [Pref] -> FreeChans Procs
fcAct []           procs = fcProcs procs
fcAct (pref:prefs) procs =
  case pref of
    Nu c d         -> cs `Set.difference` bndChans [c,d]
    Split _ c ds   -> c  `Set.insert` (cs `Set.difference` bndChans ds)
    Send c _e      -> c  `Set.insert` cs
    Recv c _xt     -> c  `Set.insert` cs
    NewSlice{}     -> error "fcAct/NewSlice undefined"
    Ax _ ds        -> l2s ds `Set.union` cs
    At _ ds        -> l2s ds `Set.union` cs
  where cs = fcAct prefs procs

zeroP :: Proc
zeroP = [] `Act` []

parP :: Proc -> Proc -> Proc
([] `Act` ps) `parP` ([] `Act` ps') = [] `Act` (ps ++ ps')
p0            `parP` p1             = [] `Act` [p0,p1]

actP :: [Pref] -> Procs -> Proc
prefs `actP` [prefs' `Act` procs] = (prefs ++ prefs') `Act` procs
prefs `actP` procs                = prefs             `Act` procs

actPs :: [Pref] -> Procs -> Procs
[]    `actPs` procs = procs
prefs `actPs` procs = [prefs `actP` procs]

filter0s :: Endom Procs
filter0s = concatMap filter0

actP0s :: [Pref] -> Procs -> Procs
actP0s prefs procs = prefs `actPs` filter0s procs

filter0 :: Proc -> Procs
filter0 (prefs `Act` procs) = prefs `actP0s` procs

suffChan :: String -> Endom Channel
suffChan s = suffName $ s ++ "#"

suffChans :: (Show i, Integral i) => i -> Channel -> [Channel]
suffChans n c = map ((`suffChan` c) . show) [0..n-1]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

split' :: TraverseKind -> Channel -> [Channel] -> Pref
split' k c = Split k c . map noSession

unRSession :: RSession -> Session
unRSession (Repl s (Lit 1)) = s
unRSession _                = error "unRSession"

-- One could generate the session annotations on the splits
fwdParTen :: [RSession] -> [Channel] -> Proc
fwdParTen _   []     = zeroP
fwdParTen rss (c:cs) = pref `actP` ps
  where
    ss     = map unRSession rss
    n      = length ss
    ds:dss = map (suffChans n) (c:cs)
    ps     = zipWith fwdP ss (transpose (ds:dss))
    pref   = split' TenK c ds : zipWith (split' ParK) cs dss

fwdRcvSnd :: Typ -> Session -> [Channel] -> Proc
fwdRcvSnd _ _ []     = zeroP
fwdRcvSnd t s (c:cs) = pref `actP` [fwdP s (c:cs)]
  where x    = prefName "x#" c
        vx   = Def x []
        pref = Recv c (Arg x t) : map (`Send` vx) cs

fwdDual :: Dual session
        => (session -> [channel] -> proc)
        ->  session -> [channel] -> proc
fwdDual f s (c:d:es) = f (dual s) (d:c:es)
fwdDual _ _ _        = error "fwdDual: Not enough channels for this forwarder (or the session is not a sink)"

fwdP :: Session -> [Channel] -> Proc
fwdP _  [] = zeroP
fwdP s0 cs =
  case s0 of
    Ten ss  ->         fwdParTen     ss cs
    Rcv t s ->         fwdRcvSnd t   s  cs
    Par ss  -> fwdDual fwdParTen     ss cs
    Snd t s -> fwdDual (fwdRcvSnd t) s  cs
    End     -> zeroP
    Atm{}   -> [ax s0 cs] `Act` []
    Seq _ss -> error "fwdP/Seq TODO"

-- The session 'Fwd n session' is a par.
-- This function builds a process which first splits this par.
fwdProc :: (Show i, Integral i) => i -> Session -> Channel -> Proc
fwdProc n s c = [split' ParK c cs] `actP` [fwdP s cs]
  where cs = suffChans n c

replProcs :: (Show i, Integral i) => i -> Name -> Procs -> Procs
replProcs n = concatMap . replProc n

replArg :: (Show i, Integral i) => i -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = map go [0..n-1] where
  go i = Arg (suffChan (show i) d) (substi (x, i) s)

replProc' :: Integral i => i -> Name -> Proc -> Procs
replProc' n x p = map go [0..n-1] where
  go i = substi (x, i) p

ax :: Session -> [Channel] -> Pref
ax s cs | validAx s cs = Ax s cs
        | otherwise    = error "ax: Not enough channels given for this forwarder (or the session is not a sink)"

splitAx :: (Show i, Integral i) => i -> Session -> Channel -> [Pref]
splitAx n s c = [split' ParK c cs, ax s cs]
  where cs = suffChans n c

dprc :: Name -> [ChanDec] -> Proc -> Dec
dprc d cs proc = Sig d Nothing (Just $ Proc cs proc)

replPref :: (Show i, Integral i) => i -> Name -> Pref -> Proc -> Proc
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
replProc n x (prefs0 `Act` procs) =
  case prefs0 of
    []           -> replProcs n x procs
    pref : prefs -> [replPref n x pref (prefs `actP` procs)]
