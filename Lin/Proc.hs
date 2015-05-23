module Lin.Proc where

import Lin.Abs (Name(Name))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe
import Data.List

import Lin.Utils
import Lin.Norm
import Lin.Subst
import Lin.Session

freeChans :: Proc -> Set Channel
freeChans (Act acts procs) = fcAct acts procs
freeChans (Ax _ c d es)    = l2s (c:d:es)
freeChans (At _ cs)        = l2s cs

bndChans :: [ChanDec] -> Set Channel
bndChans = l2s . map _argName

fcProcs :: Procs -> Set Channel
fcProcs = Set.unions . map freeChans

fcAct :: [Act] -> Procs -> Set Channel
fcAct []         procs = fcProcs procs
fcAct (act:acts) procs =
  case act of
    Nu c d         -> cs `Set.difference` bndChans [c,d]
    TenSplit c ds  -> c `Set.insert` (cs `Set.difference` bndChans ds)
    ParSplit c ds  -> c `Set.insert` (cs `Set.difference` bndChans ds)
    Send c _e      -> c `Set.insert` cs
    Recv c _xt     -> c `Set.insert` cs
    NewSlice _t _x -> error "fcAct/NewSlice undefined" -- cs ?
  where cs = fcAct acts procs

zeroP :: Proc
zeroP = Act [] []

actP :: [Pref] -> Procs -> Proc
actP pis [Act pis' procs] = Act (pis ++ pis') procs
actP pis procs            = Act pis           procs

filter0s :: Procs -> Procs
filter0s = mapMaybe filter0

filter0Act :: [Pref] -> Procs -> Maybe Proc
filter0Act prefs procs
  | null prefs && null procs' = Nothing
  | otherwise                 = Just (prefs `actP` procs')
  where procs' = filter0s procs

filter0 :: Proc -> Maybe Proc
filter0 p =
  case p of
    Act prefs procs -> filter0Act prefs procs
    Ax{}            -> Just p
    At{}            -> Just p

suffChan :: Channel -> Int -> Channel
suffChan (Name c) i = Name (c ++ show i ++ "#")

suffChans :: Channel -> Int -> [Channel]
suffChans c n = map (suffChan c) [0..n]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

parSplit' :: Channel -> [Channel] -> Pref
parSplit' c = ParSplit c . map noSession

tenSplit' :: Channel -> [Channel] -> Pref
tenSplit' c = TenSplit c . map noSession

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
    pref = tenSplit' c cs : parSplit' d ds : zipWith parSplit' es (transpose ess)

fwdRcvSnd :: Typ -> Session -> Name -> Channel -> [Name] -> Proc
fwdRcvSnd t s c d es = pref `actP` [fwdP s c d es]
  where x    = Name "x"
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
    Seq _ss -> error "fwdP/Seq TODO"

replProcs :: Int -> Name -> Procs -> Procs
replProcs n = concatMap . replProc n

substi :: Subst a => Name -> Int -> a -> a
substi x i = subst1 (x,Lit(fromIntegral i))

replArg :: Int -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = map go [0..n-1] where
  go i = Arg (suffChan d i) (substi x i s)

replProc' :: Int -> Name -> Proc -> Procs
replProc' n x p = map go [0..n-1] where
  go i = substi x i p

replPref :: Int -> Name -> Pref -> Proc -> Proc
replPref n x pref p =
  case pref of
    TenSplit c [a] -> [TenSplit c (replArg n x a)] `actP` replProc' n x p
    ParSplit c [a] -> [ParSplit c (replArg n x a)] `actP` replProc  n x p
    TenSplit{}     -> error "replPref/Ten"
    ParSplit{}     -> error "replPref/Par"
    Send _c _e     -> error "replPref/Send"
    Recv _c _xt    -> error "replPref/Recv"
    Nu _c _d       -> error "replPref/Nu"
    NewSlice _t _x -> error "replPref/NewSlice"

replProc :: Int -> Name -> Proc -> Procs
replProc n x p0 =
  case p0 of
    Act prefs0 procs ->
      case prefs0 of
        []           -> replProcs n x procs
        pref : prefs -> [replPref n x pref (Act prefs procs)]
    -- If Ax are expanded before, nothing to do here
    -- Otherwise this should do the same as the
    -- replication of the expansion.
    Ax{} -> error "replProcs/Ax"
    At{} -> error "replProcs/At"
