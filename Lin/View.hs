module Lin.View where

import Lin.Utils
import Lin.Norm

data ProcV proc
 = ActV [Pref] [proc]
 | AxV Session Channel Channel [Channel]
 | AtV Term [Channel]
  deriving (Eq,Ord,Show,Read)

unview :: ProcV Proc -> Proc
unview (ActV acts procs) = Act acts (Procs procs)
unview (AxV s c d es)    = Act [] (Ax s c d es)
unview (AtV e cs)        = Act [] (At e cs)

actV :: [Pref] -> [ProcV Proc] -> ProcV Proc
actV acts [ActV acts' procs] = ActV (acts ++ acts') procs
actV acts procs              = ActV acts (map unview procs)

actVs :: [Pref] -> [ProcV Proc] -> [ProcV Proc]
actVs []   procs = procs
actVs acts procs = [acts `actV` procs]

filter0Vs :: [Proc] -> [ProcV Proc]
filter0Vs = concatMap filter0V

filter0VProcs :: Procs -> [ProcV Proc]
filter0VProcs (Procs procs) = filter0Vs procs
filter0VProcs (Ax s c d es) = [AxV s c d es]
filter0VProcs (At e cs)     = [AtV e cs]

filter0V :: Proc -> [ProcV Proc]
filter0V (Act acts procs) = acts `actVs` filter0VProcs procs

viewProc :: Proc -> ProcV Proc
viewProc (Act acts procs) = acts `actV` filter0VProcs procs
