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

bndChans :: [ChanDec] -> Set Channel
bndChans = l2s . map _argName

fcProcs :: Procs -> Set Channel
fcProcs (Procs procs) = Set.unions $ map freeChans procs
fcProcs (Ax _ c d es) = l2s (c:d:es)
fcProcs (At _ cs)     = l2s cs

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
zeroP = Act [] (Procs [])

actP :: [Pref] -> Procs -> Proc
actP pis (Procs [Act pis' procs]) = Act (pis ++ pis') procs
actP pis procs                    = Act pis           procs

isZeroProcs :: Procs -> Bool
isZeroProcs (Procs procs) = null procs
isZeroProcs Ax{}          = False
isZeroProcs At{}          = False

filter0s :: Procs -> Procs
filter0s (Procs procs) = Procs $ mapMaybe filter0 procs
filter0s p@At{}        = p
filter0s p@Ax{}        = p

filter0 :: Proc -> Maybe Proc
filter0 (Act pis procs)
    | null pis && isZeroProcs procs' = Nothing
    | otherwise                      = Just (pis `actP` procs')
  where procs' = filter0s procs

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
fwdParTen rss c d es = pref `actP` Procs ps
  where
    ss   = map unRSession rss
    n    = length ss - 1
    cs   = suffChans c n
    ds   = suffChans d n
    ess  = map (\i -> map (`suffChan` i) es) [0..n]
    ps   = zipWith4 fwdP ss cs ds ess
    pref = tenSplit' c cs : parSplit' d ds : zipWith parSplit' es (transpose ess)

fwdRcvSnd :: Typ -> Session -> Name -> Channel -> [Name] -> Proc
fwdRcvSnd t s c d es = pref `actP` Procs [fwdP s c d es]
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

replProcs :: Int -> Name -> Procs -> [Proc]
replProcs n x ps0 =
  case ps0 of
    Procs procs -> replProc n x =<< procs
    Ax{}        -> error "replProcs/Ax"
                   -- If Ax are expanded before, nothing to do here
                   -- Otherwise this should do the same as the
                   -- replication of the expansion.
    At{}        -> error "replProcs/At"

substi :: Subst a => Name -> Int -> a -> a
substi x i = subst1 (x,Lit(fromIntegral i))

replArg :: Int -> Name -> ChanDec -> [ChanDec]
replArg n x (Arg d s) = map go [0..n-1] where
  go i = Arg (suffChan d i) (substi x i s)

replProc' :: Int -> Name -> Proc -> [Proc]
replProc' n x p = map go [0..n-1] where
  go i = substi x i p

replPref :: Int -> Name -> Pref -> Proc -> Proc
replPref n x pref p =
  case pref of
    TenSplit c [a] -> [TenSplit c (replArg n x a)] `actP` Procs (replProc' n x p)
    ParSplit c [a] -> [ParSplit c (replArg n x a)] `actP` Procs (replProc  n x p)
    TenSplit{}     -> error "replPref/Ten"
    ParSplit{}     -> error "replPref/Par"
    Send _c _e     -> error "replPref/Send"
    Recv _c _xt    -> error "replPref/Recv"
    Nu _c _d       -> error "replPref/Nu"
    NewSlice _t _x -> error "replPref/NewSlice"

replProc :: Int -> Name -> Proc -> [Proc]
replProc n x (Act prefs0 procs) =
  case prefs0 of
    []           -> replProcs n x procs
    pref : prefs -> [replPref n x pref (Act prefs procs)]
