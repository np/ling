module Ling.View where

import Ling.Utils
import Ling.Norm

data ProcV proc
 = ActV [Pref] [proc]
 | AxV Session Channel Channel [Channel]
 | AtV Term [Channel]
  deriving (Eq,Ord,Show,Read)

unview :: ProcV Proc -> Proc
unview (ActV prefs procs) = Act prefs procs
unview (AxV s c d es)     = Ax s c d es
unview (AtV e cs)         = At e cs

actV :: [Pref] -> [ProcV Proc] -> ProcV Proc
actV prefs [ActV prefs' procs] = ActV (prefs ++ prefs') procs
actV prefs procs               = ActV prefs (map unview procs)

actVs :: [Pref] -> [ProcV Proc] -> [ProcV Proc]
actVs []    procs = procs
actVs prefs procs = [prefs `actV` procs]

filter0Vs :: [Proc] -> [ProcV Proc]
filter0Vs = concatMap filter0V

filter0V :: Proc -> [ProcV Proc]
filter0V (Act prefs procs) = prefs `actVs` filter0Vs procs
filter0V (Ax s c d es)     = [AxV s c d es]
filter0V (At e cs)         = [AtV e cs]

viewProc :: Proc -> ProcV Proc
viewProc (Act prefs procs) = prefs `actV` filter0Vs procs
viewProc (Ax s c d es)     = AxV s c d es
viewProc (At e cs)         = AtV e cs
