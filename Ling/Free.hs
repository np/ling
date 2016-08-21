{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE TemplateHaskell  #-}

module Ling.Free where

import           Ling.Norm
import           Ling.Prelude
import qualified Data.Set as Set

data BoundFree n
  = Bound { _nName :: n }
  | Free  { _nName :: n }
  deriving (Eq,Ord,Show,Read)

makePrisms ''BoundFree
makeLenses ''BoundFree

type Names n a = Fold a (BoundFree n)
type Vars    a = Names Name    a
type Chans   a = Names Channel a

pattChans :: Fold CPatt Name
pattChans f = \case
  ArrayP k ps -> ArrayP k <$> (each . pattChans) f ps
  ChanP cd    -> ChanP    <$> cdChan f cd

fcAct :: Fold Act Channel
fcAct = actChans . _Free

bcAct :: Fold Act Channel
bcAct = actChans . _Bound

actChans :: Chans Act
actChans f = \case
  Split c pat     -> Split <$> re _Free f c <*> (pattChans . re _Bound) f pat
  Send c os t     -> (\c' -> Send c' os t) <$> re _Free f c
  Recv c vd       -> (`Recv` vd)           <$> re _Free f c
  Ax s cs         -> Ax s                  <$> (each . re _Free) f cs
  At t p          -> At t                  <$> (pattChans . re _Free) f p
  Nu ann newpatt  -> Nu ann                <$> newPattChans f newpatt

newPattChans :: Chans NewPatt
newPattChans f = \case
  NewChans k cs -> NewChans  k    <$> (each . cdChan . re _Bound) f cs
  NewChan c mt  -> (`NewChan` mt) <$> re _Bound f c

bvDefs :: Fold Defs Name
bvDefs = to (\defs -> keysSet (defs ^. defsMap)) . folded

bvAct :: Fold Act Name
bvAct f = \case
  Recv os x      -> Recv os <$> argName f x
  a@Nu{}         -> pure a
  a@Split{}      -> pure a
  a@Send{}       -> pure a
  a@Ax{}         -> pure a
  a@At{}         -> pure a

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
--bvPref :: Fold Pref Name
--bvPref    = _Prll . each . bvAct
--prefChans :: BoundChans Pref
--prefChans = _Prll . each . prefChan
--fcPref :: FreeChans Pref
--fcPref = _Prll . each . fcAct

bcProc :: Fold Proc Channel
bcProc f = \case
  Act act      -> Act <$> bcAct f act
  Procs procs  -> Procs <$> bcProcs f procs
  p@NewSlice{} -> pure p
  Dot{}        -> error "bcProc: Dot"
  LetP defs p  -> LetP defs <$> bcProc f p

bcProcs :: Fold Procs Channel
bcProcs = _Prll . each . bcProc

bvProc :: Fold Proc Name
bvProc f = \case
  Act act           -> Act <$> bvAct f act
  Procs procs       -> Procs <$> bvProcs f procs
  p@NewSlice{}      -> pure p
  proc0 `Dot` proc1 -> Dot <$> bvProc f proc0 <*> bvProc f proc1
  LetP defs p       -> LetP defs <$> bvProc f p

bvProcs :: Fold Procs Name
bvProcs = _Prll . each . bvProc

fcProc :: Fold Proc Channel
fcProc = to fcProcSet . folded

fcProcSet :: Proc -> Set Channel
fcProcSet = \case
  Act act           -> setOf fcAct act
  proc0 `Dot` proc1 -> fcProcSet proc0 <>
                       (fcProcSet proc1 `Set.difference` setOf bcProc proc0)
  NewSlice cs _ _ p -> setOf each cs <> fcProcSet p
  Procs procs       -> setOf (_Prll . each . fcProc) procs
  LetP _ p          -> fcProcSet p
-- -}
