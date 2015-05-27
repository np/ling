module Lin.Proc where

import Lin.Abs (Name(Name))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List

import Lin.Utils
import Lin.Norm
import Lin.Subst
import Lin.Session

freeChans :: Proc -> Set Channel
freeChans (prefs `Act` procs) = fcAct prefs procs
freeChans (Ax _ c d es)       = l2s (c:d:es)
freeChans (At _ cs)           = l2s cs

bndChans :: [ChanDec] -> Set Channel
bndChans = l2s . map _argName

fcProcs :: Procs -> Set Channel
fcProcs = Set.unions . map freeChans

fcAct :: [Pref] -> Procs -> Set Channel
fcAct []           procs = fcProcs procs
fcAct (pref:prefs) procs =
  case pref of
    Nu c d         -> cs `Set.difference` bndChans [c,d]
    Split _ c ds   -> c  `Set.insert` (cs `Set.difference` bndChans ds)
    Send c _e      -> c  `Set.insert` cs
    Recv c _xt     -> c  `Set.insert` cs
    NewSlice _t _x -> error "fcAct/NewSlice undefined" -- cs ?
  where cs = fcAct prefs procs

zeroP :: Proc
zeroP = [] `Act` []

actP :: [Pref] -> Procs -> Proc
prefs `actP` [prefs' `Act` procs] = (prefs ++ prefs') `Act` procs
prefs `actP` procs                = prefs             `Act` procs

actPs :: [Pref] -> Procs -> Procs
[]    `actPs` procs = procs
prefs `actPs` procs = [prefs `actP` procs]

filter0s :: Procs -> Procs
filter0s = concatMap filter0

actP0s :: [Pref] -> Procs -> Procs
actP0s prefs procs = prefs `actPs` filter0s procs

filter0 :: Proc -> Procs
filter0 p = case p of
  prefs `Act` procs -> prefs `actP0s` procs
  Ax{}              -> [p]
  At{}              -> [p]

suffChan :: Channel -> Int -> Channel
suffChan (Name c) i = Name (c ++ show i ++ "#")

suffChans :: Channel -> Int -> [Channel]
suffChans c n = map (suffChan c) [0..n]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

split' :: TraverseKind -> Channel -> [Channel] -> Pref
split' k c = Split k c . map noSession

unRSession :: RSession -> Session
unRSession (Repl s (Lit 1)) = s
unRSession _                = error "unRSession"

-- One could generate the session annotations on the splits
fwdParTen :: [RSession] -> Channel -> Channel -> [Channel] -> Proc
fwdParTen rss c d es = pref `actP` ps
  where
    ss   = map unRSession rss
    n    = length ss - 1
    cs   = suffChans c n
    ds   = suffChans d n
    ess  = map (\i -> map (`suffChan` i) es) [0..n]
    ps   = zipWith4 fwdP ss cs ds ess
    pref = split' TenK c cs : split' ParK d ds : zipWith (split' ParK) es (transpose ess)

fwdRcvSnd :: Typ -> Session -> Channel -> Channel -> [Name] -> Proc
fwdRcvSnd t s c d es = pref `actP` [fwdP s c d es]
  where x    = Name $ "x#" ++ unName c -- ++ "#" ++ unName d
        vx   = Def x []
        pref = Recv c (Arg x t) : Send d vx : map (`Send` vx) es

fwdP :: Session -> Channel -> Channel -> [Channel] -> Proc
fwdP s0 c d es =
  case s0 of
    Ten ss  -> fwdParTen ss         c d es
    Par ss  -> fwdParTen (dual ss)  d c es
    Rcv t s -> fwdRcvSnd t s        c d es
    Snd t s -> fwdRcvSnd t (dual s) d c es
    End     -> zeroP
    Atm{}   -> Ax s0 c d es
    Seq _ss -> error "fwdP/Seq TODO"

replProcs :: Int -> Name -> Procs -> Procs
replProcs n = concatMap . replProc n

substi :: Subst a => (Name, Int) -> a -> a
substi (x, i) = subst1 (x, Lit(fromIntegral i))

replArg :: Int -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = map go [0..n-1] where
  go i = Arg (suffChan d i) (substi (x, i) s)

replProc' :: Int -> Name -> Proc -> Procs
replProc' n x p = map go [0..n-1] where
  go i = substi (x, i) p

replPref :: Int -> Name -> Pref -> Proc -> Proc
replPref n x pref p =
  case pref of
    Split k c [a]  -> [Split k c (replArg n x a)] `actP` replProc' n x p
    Split{}        -> error "replPref/Split"
    Send _c _e     -> error "replPref/Send"
    Recv _c _xt    -> error "replPref/Recv"
    Nu _c _d       -> error "replPref/Nu"
    NewSlice _t _x -> error "replPref/NewSlice"

replProc :: Int -> Name -> Proc -> Procs
replProc n x p0 =
  case p0 of
    prefs0 `Act` procs ->
      case prefs0 of
        []           -> replProcs n x procs
        pref : prefs -> [replPref n x pref (prefs `Act` procs)]
    -- If Ax are expanded before, nothing to do here
    -- Otherwise this should do the same as the
    -- replication of the expansion.
    -- This might be needed because of abstract sessions.
    Ax{} -> error "replProcs/Ax"
    At{} -> error "replProcs/At"
