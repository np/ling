module Ling.Print.Instances where

import           Data.Map    (Map)
import           Data.Set    (Set)
import           Ling.Norm
import           Ling.Print
import           Ling.Reify
import           Ling.Scoped
import           Ling.Utils

txt :: String -> Doc
txt = doc . showString

nl :: Doc
nl = txt "\n"

prtSeq :: Doc -> Doc -> Doc -> [Doc] -> Doc
prtSeq p b e []     = concatD [p, b, e]
prtSeq p b e [x]    = concatD [p, b, x, e]
prtSeq p b e (x:xs) = concatD $  [nl, p, b, txt " ", x]
                              ++ [z | y <- xs, z <- [nl, p, txt ",", y]]
                              ++ [nl, p, e]

prtLst :: Print a => [a] -> Doc
prtLst = prtSeq (txt "  ") id id . map (prt 0)

instance (Ord a, Print a) => Print (Set a) where
  prt _i = prtSeq (txt "  ") (txt "⦃") (txt "⦄") . map (prt 0) . s2l

instance (Ord k, Print k, Print v) => Print (Map k v) where
  prt _i = prtSeq (txt "  ") (txt "⦃") (txt "⦄") . map prettyKV . m2l
    where prettyKV (k,v) = prt 0 k . txt " ↦ " . prt 0 v

instance Print a => Print (Scoped a) where
  prt _i (Scoped ld x) =
    concatD [ doc (showString "let ") , prt 0 ld
            , doc (showString "in")
            , prt 0 x ]

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

instance Print Dec where
  prt     i = prt i . reifyDec
  prtList i = prtList i . map reifyDec

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
