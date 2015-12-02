module Ling.Proc
  ( asProcs
  , actP
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
  , split'
  , fwdP
  , fwdProc
  , ax
  , splitAx
  ) where

import Data.Set (member, insert)

import Ling.Prelude
import Ling.Norm
import Ling.Session

asProcs :: Proc -> [Proc]
asProcs ([] `Dot` procs) = procs
asProcs proc             = [proc]

infixr 4 `prllActP`

prllActP :: [Act] -> Procs -> Proc
[]   `prllActP` procs = mconcat procs
acts `prllActP` procs = acts `Dot` procs

infixr 4 `prllActPs`

prllActPs :: [Act] -> Endom Procs
[]   `prllActPs` procs = procs
acts `prllActPs` procs = [acts `prllActP` procs]

infixr 4 `actP`

actP :: Act -> Procs -> Proc
act `actP` procs = [act] `Dot` procs

infixr 4 `actsP`

actsP :: [Act] -> Procs -> Proc
[]       `actsP` procs = mconcat procs
act:acts `actsP` procs = act `actP` asProcs (acts `actsP` procs)

infixr 4 `actPs`

actPs :: Act -> Endom Procs
act `actPs` procs = [act `actP` procs]

infixr 4 `actsPs`

actsPs :: [Act] -> Endom Procs
[]   `actsPs` procs = procs
acts `actsPs` procs = [acts `actsP` procs]

infixr 4 `dotP`

dotP :: Op2 Proc
(pref0 `Dot` procs0) `dotP` proc1 = pref0 `prllActP` (procs0 `prllDotP` proc1)

infixr 4 `dotsP`

dotsP :: [Proc] -> Proc
dotsP = foldr dotP ø

infixr 4 `prllDotP`

prllDotP :: Procs -> Proc -> Procs
prllDotP []  p  = asProcs p
prllDotP [p] p' = [p `dotP` p']
prllDotP ps  p'
  | Just prefs <- mapM justPref ps
      = [concat prefs `prllActP` asProcs p']
prllDotP ps p' =
  error . unlines $
    ["Unsupported sequencing of parallel processes"
    ,show ps
    ,show p'
    ]

-- Is a given process only a prefix?
justPref :: Proc -> Maybe Pref
justPref (pref `Dot` []) = Just pref
justPref _               = Nothing

infixr 4 `nxtP`

nxtP :: Proc -> Endom Proc
(pref0 `Dot` procs0) `nxtP` p1 = pref0 `prllActP` [procs0 `prllNxtP` p1]

infixr 4 `prllNxtP`

prllNxtP :: Procs -> Endom Proc
prllNxtP ps p = case ps of
  []   -> p
  [p0] -> p0 `nxtP` p
  _    -> error "prllNxtP: Cannot sequence parallel processes"

-- TODO: filtering 0-processes should not be necessary they should
-- not be part of the normal form.
filter0s :: Endom Procs
filter0s = concatMap filter0

filter0 :: Proc -> Procs
filter0 ([]   `Dot` procs) = filter0s procs
filter0 (acts `Dot` procs) = acts `prllActPs` filter0s procs

subChans :: (Show i, Integral i) => i -> Channel -> [Channel]
subChans n c = [ suffixedChan (show i ++ "#") # c | i <- [0..n-1] ]

noSession :: Channel -> ChanDec
noSession c = Arg c Nothing

split' :: TraverseKind -> Channel -> [Channel] -> Act
split' k c = Split k c . map noSession

unRSession :: RSession -> Session
unRSession (s `Repl` r)
  | litR1 `is` r = s
  | otherwise    = error "unRSession"

type UsedNames = Set Name

avoidUsed :: Name -> Name -> UsedNames -> (Name, UsedNames)
avoidUsed suggestion basename used = go allNames where
  allPrefixes = ["x#", "y#", "z#"] ++ (((++"#") . ("x"++) . show) <$> [0 :: Int ..])
  allNames = (if suggestion == anonName then id else (suggestion :)) $
             [ prefixedName p # basename | p <- allPrefixes ]
  go names | x `member` used = go (tail names)
           | otherwise       = (x, insert x used)
    where x = head names

-- One could generate the session annotations on the splits
fwdSplit :: [TraverseKind] -> Endom Procs -> UsedNames -> [RSession] -> [Channel] -> Proc
fwdSplit ks fprocs used rss cs
  | null cs   = ø
  | otherwise = pref `actsP` fprocs ps
  -- These splits are independant, they are put in sequence because
  -- splitting always commutes anyway.
  where
    ss   = unRSession <$> rss
    dss  = subChans (length ss) <$> cs
    ps   = zipWith     (fwdP used) ss (transpose dss)
    pref = zipWith3 id (split' <$> ks) cs dss

fwdParTen, fwdSeqSeq :: UsedNames -> [RSession] -> [Channel] -> Proc
fwdParTen = fwdSplit (TenK : repeat ParK) id
fwdSeqSeq = fwdSplit (repeat SeqK) (asProcs . dotsP)

fwdIO :: RW -> UsedNames -> VarDec -> Session -> [Channel] -> Proc
fwdIO _     _    _   _ []     = ø
fwdIO Write used arg s ds     = fwdDual (fwdIO Read used arg) s ds
fwdIO Read  used arg s (c:ds) = recv `actP` sends `prllActPs` [fwdP used' s (c:ds)]
  where (x, used') = avoidUsed (arg^.argName) c used
        vx         = Def x []
        recv       = Recv c (arg & argName .~ x)
        sends      = [ Send d vx | d <- ds ]

fwdDual :: Dual session
        => (session -> [channel] -> proc)
        ->  session -> [channel] -> proc
fwdDual f s (c:d:es) = f (dual s) (d:c:es)
fwdDual _ _ _        = error "fwdDual: Not enough channels for this forwarder (or the session is not a sink)"

fwdArray :: TraverseKind -> UsedNames -> [RSession] -> [Channel] -> Proc
fwdArray k = case k of
  SeqK -> fwdSeqSeq
  TenK -> fwdParTen
  ParK -> fwdDual . fwdParTen

fwdP :: UsedNames -> Session -> [Channel] -> Proc
fwdP _    _  [] = ø
fwdP used s0 cs
  | endS `is` s0 = ø
  | otherwise    =
  case s0 of
    Array k ss -> fwdArray k used ss cs
    IO p t s   -> fwdIO p used t s cs
    TermS{}    -> [ax s0 cs] `Dot` []

-- The session 'Fwd n session' is a par.
-- This function builds a process which first splits this par.
fwdProc :: (Show i, Integral i) => i -> Session -> Channel -> Proc
fwdProc n s c = split' ParK c cs `actP` [fwdP ø s cs]
  where cs = subChans n c

ax :: Session -> [Channel] -> Act
ax s cs | validAx s cs = Ax s cs
        | otherwise    = error "ax: Not enough channels given for this forwarder (or the session is not a sink)"

splitAx :: (Show i, Integral i) => i -> Session -> Channel -> [Act]
splitAx n s c = [split' ParK c cs, ax s cs]
  where cs = subChans n c

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
replProc n x (pref0 `Dot` procs) =
  case pref0 of
    []    -> replProcs n x procs
    [act] -> [replPref n x act procs]
  --  act : pref -> [replPref n x act (pref `actP` procs)]
-}
