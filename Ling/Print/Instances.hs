module Ling.Print.Instances where

import Ling.Print
import Ling.Utils
import Ling.Norm
import Ling.Reify

-- Unused
instance Print a => Print (Arg a) where
  prt _i (Arg ident x) =
    concatD [ doc (showString "(") , prt 0 ident , doc (showString ":")
            , prt 0 x , doc (showString ")") ]

  prtList _ = concatD . map (prt 0)

instance (Print a,Print b,Print c) => Print (a,b,c) where
  prt _i (a,b,c) =
    concatD [ doc (showString "(") , prt 0 a
            , doc (showString ",") , prt 0 b
            , doc (showString ",") , prt 0 c
            , doc (showString ")") ]

instance Print Session where
  prt     i = prt i . reifySession
  prtList i = prtList i . reifySessions

instance Print RSession where
  prt     i = prt i . reifyRSession
  prtList i = prtList i . reifyRSessions

instance Print Pref where
  prt     i = prt i . reifyPref
  prtList i = prtList i . map reifyPref

instance Print Proc where
  prt     i = prt i . reifyProc
  prtList i = prtList i . map reifyProc

instance Print Program where
  prt     i = prt i . reifyProgram
  prtList i = prtList i . map reifyProgram

instance Print Term where
  prt     i = prt i . reifyTerm
  prtList i = prtList i . map reifyTerm
{-  e = case e of
   Lit n -> prPrec i 3 (concatD [prt 0 n])
   Ann term0 term -> prPrec i 3 (concatD [doc (showString "(") , prt 0 term0 , doc (showString ":") , prt 0 term , doc (showString ")")])
   Typ  -> prPrec i 3 (concatD [doc (showString "Type")])
   Proto sessions -> prPrec i 3 (concatD [doc (showString "<") , prt 0 sessions , doc (showString ">")])
   Def ident []    -> prPrec i 3 (prt 0 ident)
   Def ident terms -> prPrec i 2 (concatD [prt 0 ident , prt 0 terms])
   Proc ids proc -> prPrec i 0 (concatD [doc (showString "(") , prt 0 ids , doc (showString ")") , doc (showString ".") , prt 0 proc])
   Fun arg term -> prPrec i 0 (concatD [prt 0 arg , doc (showString " ->") , prt 0 term])
   Sig arg term -> prPrec i 0 (concatD [prt 0 arg , doc (showString " *") , prt 0 term])
  prtList _ es = case es of
   [] -> (concatD [])
   x:xs -> (concatD [prt 3 x , prt 0 xs])
-}
