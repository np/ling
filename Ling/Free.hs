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
bcChanDecs = setOf (each . cdChan)

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
  Ax _ cs         -> l2s cs
  At _ p          -> fcPat p
  LetA{}          -> ø

bcAct :: BoundChans Act
bcAct = \case
  Nu _ cs      -> bcChanDecs cs
  Split _ _ ds -> bcChanDecs ds
  Send{}       -> ø
  Recv{}       -> ø
  Ax{}         -> ø
  At{}         -> ø
  LetA{}       -> ø

bvAct :: BoundVars Act
bvAct = \case
  Nu{}           -> ø
  Split{}        -> ø
  Send{}         -> ø
  Recv _ x       -> bvVarDec x
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
bvPref = mconcat . map bvAct . view unPrll

bcPref = mconcat . map bcAct . view unPrll

fcPref = mconcat . map fcAct . view unPrll

bcProc :: BoundChans Proc
bcProc = \case
  Act act     -> bcAct act
  Procs procs -> bcProcs procs
  NewSlice{}  -> ø
  Dot{}       -> error "bcProc: Dot"

bcProcs :: BoundChans Procs
bcProcs = mconcat . map bcProc . view unPrll

bvProc :: BoundVars Proc
bvProc = \case
  Act act     -> bvAct act
  Procs procs -> bvProcs procs
  NewSlice{}  -> ø
  Dot{}       -> error "bvProc: Dot"

bvProcs :: BoundVars Procs
bvProcs = mconcat . map bvProc . view unPrll

fcProc :: FreeChans Proc
fcProc = \case
  Act act           -> fcAct act
  proc0 `Dot` proc1 -> fcProc proc0 <> (fcProc proc1 `Set.difference` bcProc proc0)
  NewSlice cs _ _ p -> l2s cs <> fcProc p
  Procs procs       -> fcProcs procs

fcProcs :: FreeChans Procs
fcProcs = mconcat . map fcProc . view unPrll
