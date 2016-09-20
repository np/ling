{-# LANGUAGE LambdaCase #-}
module Ling.Fwd
  ( fwdP
  , fwdProc
  , fwdProc'
  ) where

import Prelude hiding (pred)
import Ling.Norm
import Ling.Prelude
import Ling.Proc
import Ling.Session.Core

type MkFwd a = (Session -> Session) -> UsedNames -> a -> [Channel] -> Proc

fwdSplit :: ([Proc] -> Proc) -> [TraverseKind] -> MkFwd Sessions
fwdSplit fprocs ks redSession used (Sessions rss) cs
  | null cs   = ø
  | null rss  = toProc $ Order (zipWith3 splitK ks cs (repeat []))
  | otherwise = Order pref `dotP` fprocs ps
  -- These splits are independant, they are put in sequence because
  -- splitting always commutes anyway.
  where
    cdss = zipWith subChanDecs (transpose (fwds (length cs) <$> rss)) cs
    css  = map _cdChan <$> cdss
    ps   = zipWith3 (\k -> fwdR k redSession used) ks rss (transpose css)
    pref = zipWith3 splitK ks cs cdss

fwdIO :: MkFwd (RW, VarDec, Session)
fwdIO _          _    _               []       = ø
fwdIO redSession used (Write, arg, s) (c:d:es) = fwdIO redSession used (Read, arg, dual s) (d:c:es)
fwdIO redSession used (Read,  arg, s) (c:ds)   = recv `dotP` Prll sends `dotP` fwdP redSession used' s (c:ds)
  where (x, used') = avoidUsed (arg^.argName) c used
        vx         = mkVar x
        recv       = Recv c (arg & argName .~ x)
        sends      = [ Send d Nothing vx | d <- ds ]
fwdIO _          _    _               _        = error "fwdIO: Not enough channels for this forwarder (or the session is not a sink)"

fwdArray :: TraverseKind -> MkFwd Sessions
fwdArray = \case
  SeqK -> fwdSplit dotsP   $ repeat SeqK
  TenK -> fwdSplit mconcat $ TenK : repeat ParK
  ParK -> fwdSplit mconcat $ ParK : TenK : repeat ParK

fwdR :: TraverseKind -> MkFwd RSession
fwdR k redSession used (s `Repl` r)
  | litR1 `is` r = fwdP redSession used s
  | otherwise    = mkReplicate k r anonName . fwdP redSession used s

fwdP :: MkFwd Session
fwdP _          _    _  [] = ø
fwdP redSession used s0 cs
  | endS `is` s0 = ø
  | otherwise    =
  case redSession s0 of
    Array k ss -> fwdArray k redSession used ss cs
    IO p t s   -> fwdIO redSession used (p, t, s) cs
    TermS{}    -> Act $ Ax s0 cs

fwdProc' :: (Session -> Session) -> Session -> [Channel] -> Proc
fwdProc' redSession s cs = fwdP redSession ø s cs

-- The session 'Fwd n session' is a par.
-- This function builds a process which first splits this par.
fwdProc :: Int -> Session -> Channel -> Proc
fwdProc n s c = splitK ParK c cs `dotP` fwdP id ø s (_cdChan <$> cs)
  where
    ss = oneS <$> fwds n s
    cs = subChanDecs ss c
