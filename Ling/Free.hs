{-# LANGUAGE LambdaCase #-}

module Ling.Free where

import qualified Data.Set     as Set
import           Ling.Norm
import           Ling.Prelude

type FreeChans a = a -> Set Channel

type BoundChans a = FreeChans a

type FreeVars a = FreeChans a

type BoundVars a = FreeChans a

bvVarDec :: BoundChans VarDec
bvVarDec = l2s . pure . _argName

bcChanDecs :: BoundChans [ChanDec]
bcChanDecs = l2s . map _argName

fcPat :: FreeChans CPatt
fcPat = \case
  ArrayP _ ps -> fcPats ps
  ChanP cd    -> bcChanDecs [cd]

fcPats :: FreeChans [CPatt]
fcPats = mconcat . map fcPat

fcAct :: FreeChans Act
fcAct = \case
  Nu{}            -> ø
  Split _ c _     -> l2s [c]
  Send c _        -> l2s [c]
  Recv c _        -> l2s [c]
  NewSlice cs _ _ -> l2s cs
  Ax _ cs         -> l2s cs
  At _ p          -> fcPat p
  LetA{}          -> ø

bcAct :: BoundChans Act
bcAct = \case
  Nu c d       -> bcChanDecs [c, d]
  Split _ _ ds -> bcChanDecs ds
  Send{}       -> ø
  Recv{}       -> ø
  NewSlice{}   -> ø
  Ax{}         -> ø
  At{}         -> ø
  LetA{}       -> ø

bvAct :: BoundVars Act
bvAct = \case
  Nu{}           -> ø
  Split{}        -> ø
  Send{}         -> ø
  Recv _ x       -> bvVarDec x
  NewSlice _ _ x -> l2s [x]
  Ax{}           -> ø
  At{}           -> ø
  LetA defs      -> keysSet (defs ^. defsMap)

{-
fvAct :: FreeVars Act
fvAct = \case
  Nu{}            -> ø
  Split{}         -> ø
  Send _ tm       -> fvTerm tm
  Recv _ x        -> fvVarDec x
  NewSlice _ tm _ -> fvTerm tm
  Ax s _          -> fvSession s
  At tm _         -> fvTerm tm
-}
-- The actions are in parallel. Also they are supposed be disjoint.
bvPref :: BoundVars Pref
bcPref :: BoundChans Pref
fcPref :: FreeChans Pref
bvPref = mconcat . map bvAct

bcPref = mconcat . map bcAct

fcPref = mconcat . map fcAct

fcProc :: FreeChans Proc
fcProc (pref `Dot` procs) =
  fcPref pref <> (fcProcs procs `Set.difference` bcPref pref)

fcProcs :: FreeChans Procs
fcProcs = mconcat . map fcProc
