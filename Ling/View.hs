module Ling.View where

import Ling.Utils
import Ling.Norm

data ProcV proc
 = ActV [Pref] [proc]
 | AxV Session Channel Channel [Channel]
 | AtV Term [Channel]
  deriving (Eq,Ord,Show,Read)

unview :: ProcV Proc -> Proc
unview (ActV acts procs) = Act acts procs
unview (AxV s c d es)    = Ax s c d es
unview (AtV e cs)        = At e cs

actV :: [Pref] -> [ProcV Proc] -> ProcV Proc
actV acts [ActV acts' procs] = ActV (acts ++ acts') procs
actV acts procs              = ActV acts (map unview procs)

actVs :: [Pref] -> [ProcV Proc] -> [ProcV Proc]
actVs []   procs = procs
actVs acts procs = [acts `actV` procs]

filter0Vs :: [Proc] -> [ProcV Proc]
filter0Vs = concatMap filter0V

filter0V :: Proc -> [ProcV Proc]
filter0V (Act acts procs) = acts `actVs` filter0Vs procs
filter0V (Ax s c d es)    = [AxV s c d es]
filter0V (At e cs)        = [AtV e cs]

viewProc :: Proc -> ProcV Proc
viewProc (Act acts procs) = acts `actV` filter0Vs procs
viewProc (Ax s c d es)    = AxV s c d es
viewProc (At e cs)        = AtV e cs
