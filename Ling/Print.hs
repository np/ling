{-# OPTIONS -fno-warn-orphans #-}
-- See Ling.Print.Class about how this module has been changed
module Ling.Print (module Ling.Print.Class) where

import           Ling.Abs
import qualified Ling.Norm as N
import           Ling.Prelude
import           Ling.Print.Class
import           Ling.Reify
import           Ling.Scoped


instance Print OpName where
  prt _ (OpName i) = doc (showString ( i))



instance Print Program where
  prt i e = case e of
    Prg decs -> prPrec i 0 (concatD [prt 0 decs])

instance Print Dec where
  prt i e = case e of
    DDef name optsig term -> prPrec i 0 (concatD [prt 0 name, prt 0 optsig, txt "=\n", prt 0 term])
    DSig name term -> prPrec i 0 (concatD [prt 0 name, txt ": ", prt 0 term])
    DDat name connames -> prPrec i 0 (concatD [doc (showString "data"), prt 0 name, doc (showString "="), prt 0 connames])
    DAsr assertion -> prPrec i 0 (concatD [txt "assert", txt "+\n", prt 0 assertion, txt "-\n"])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, txt ",\n\n", prt 0 xs])
instance Print Assertion where
  prt i e = case e of
    AEq term1 term2 optsig -> prPrec i 0 (concatD [prt 0 term1, nl, txt "=\n", prt 0 term2, txt "\n", prt 0 optsig])

instance Print ConName where
  prt i e = case e of
    CN name -> prPrec i 0 (concatD [doc (showString "`"), prt 0 name])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString "|"), prt 0 xs])
instance Print OptSig where
  prt i e = case e of
    NoSig -> prPrec i 0 (concatD [])
    SoSig term -> prPrec i 0 (concatD [txt ": ", prt 0 term])

instance Print VarDec where
  prt i e = case e of
    VD name optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 optsig, doc (showString ")")])

instance Print ChanDec where
  prt i e = case e of
    CD name optrepl optsession -> prPrec i 0 (concatD [prt 0 name, prt 0 optrepl, prt 0 optsession])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print Branch where
  prt i e = case e of
    Br conname term -> prPrec i 0 (concatD [prt 0 conname, doc (showString "->"), prt 0 term])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, txt ",\n", prt 0 xs])
instance Print Literal where
  prt i e = case e of
    LInteger n -> prPrec i 0 (concatD [prt 0 n])
    LDouble d -> prPrec i 0 (concatD [prt 0 d])
    LString str -> prPrec i 0 (concatD [prt 0 str])
    LChar c -> prPrec i 0 (concatD [prt 0 c])

instance Print ATerm where
  prt i e = case e of
    Var name -> prPrec i 0 (concatD [prt 0 name])
    Op opname -> prPrec i 0 (concatD [prt 0 opname])
    Lit literal -> prPrec i 0 (concatD [prt 0 literal])
    Con conname -> prPrec i 0 (concatD [prt 0 conname])
    TTyp -> prPrec i 0 (concatD [doc (showString "Type")])
    TProto rsessions -> prPrec i 0 (concatD [doc (showString "<"), prt 0 rsessions, doc (showString ">")])
    Paren term optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")")])
    End -> prPrec i 0 (concatD [doc (showString "end")])
    Par rsessions -> prPrec i 0 (concatD [doc (showString "{"), prt 0 rsessions, doc (showString "}")])
    Ten rsessions -> prPrec i 0 (concatD [doc (showString "["), prt 0 rsessions, doc (showString "]")])
    Seq rsessions -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 rsessions, doc (showString ":]")])
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])
instance Print Term where
  prt i e = case e of
    RawApp aterm aterms -> prPrec i 3 (concatD [prt 0 aterm, prt 0 aterms])
    Case term branchs -> prPrec i 2 (concatD [txt "case", prt 0 term, txt "of", txt "{\n", prt 0 branchs, txt "\n}"])
    Snd term csession -> prPrec i 2 (concatD [doc (showString "!"), prt 3 term, prt 0 csession])
    Rcv term csession -> prPrec i 2 (concatD [doc (showString "?"), prt 3 term, prt 0 csession])
    Dual term -> prPrec i 2 (concatD [doc (showString "~"), prt 2 term])
    TRecv name -> prPrec i 2 (concatD [doc (showString "<-"), prt 0 name])
    Loli term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "-o"), prt 1 term2])
    TFun term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "->"), prt 1 term2])
    TSig term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "**"), prt 1 term2])
    Let name optsig term1 term2 -> prPrec i 1 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 term1, doc (showString "in"), prt 0 term2])
    Lam term1 term2 -> prPrec i 0 (concatD [doc (showString "\\"), prt 2 term1, doc (showString "->"), prt 0 term2])
    TProc chandecs proc -> prPrec i 0 (concatD [txt "proc", txt "(", prt 0 chandecs, txt ")", nl, prt 0 proc])

instance Print Proc where
  prt i e = case e of
    PAct act -> prPrec i 1 (concatD [prt 0 act])
    PPrll procs -> prPrec i 1 (concatD [txt "(\n", prt 0 procs, txt "\n)"])
    PNxt proc1 proc2 -> prPrec i 0 (concatD [prt 1 proc1, txt "\n", prt 0 proc2])
    PDot proc1 proc2 -> prPrec i 0 (concatD [prt 1 proc1, txt ".\n", prt 0 proc2])
    PSem proc1 proc2 -> prPrec i 0 (concatD [prt 1 proc1, txt ";\n", prt 0 proc2])
    NewSlice chandecs aterm name proc -> prPrec i 0 (concatD [txt "slice", txt "(", prt 0 chandecs, txt ")", prt 0 aterm, txt "as", prt 0 name, txt "+\n", prt 0 proc, txt "-\n"])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, txt "\n|", prt 0 xs])
instance Print Act where
  prt i e = case e of
    Nu newalloc -> prPrec i 0 (concatD [prt 0 newalloc])
    Split split -> prPrec i 0 (concatD [prt 0 split])
    Send name aterm -> prPrec i 0 (concatD [doc (showString "send"), prt 0 name, prt 0 aterm])
    NewSend name optsession aterm -> prPrec i 0 (concatD [prt 0 name, prt 0 optsession, doc (showString "<-"), prt 0 aterm])
    Recv name vardec -> prPrec i 0 (concatD [doc (showString "recv"), prt 0 name, prt 0 vardec])
    NewRecv name1 optsig name2 -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name1, prt 0 optsig, doc (showString "<-"), prt 0 name2])
    LetRecv name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "<="), prt 0 aterm])
    Ax asession chandecs -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 asession, doc (showString "("), prt 0 chandecs, doc (showString ")")])
    SplitAx n asession name -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 n, prt 0 asession, prt 0 name])
    At aterm topcpatt -> prPrec i 0 (concatD [doc (showString "@"), prt 0 aterm, prt 0 topcpatt])
    LetA name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 aterm])

instance Print ASession where
  prt i e = case e of
    AS aterm -> prPrec i 0 (concatD [prt 0 aterm])

instance Print Split where
  prt i e = case e of
    PatSplit name optas cpatt -> prPrec i 0 (concatD [doc (showString "split"), prt 0 name, prt 0 optas, prt 0 cpatt])
    ParSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "{"), prt 0 chandecs, doc (showString "}")])
    TenSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "["), prt 0 chandecs, doc (showString "]")])
    SeqSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "[:"), prt 0 chandecs, doc (showString ":]")])

instance Print OptAs where
  prt i e = case e of
    NoAs -> prPrec i 0 (concatD [])
    SoAs -> prPrec i 0 (concatD [doc (showString "as")])

instance Print TopCPatt where
  prt i e = case e of
    OldTopPatt chandecs -> prPrec i 0 (concatD [doc (showString "("), prt 0 chandecs, doc (showString ")")])
    ParTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    TenTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    SeqTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])

instance Print CPatt where
  prt i e = case e of
    ChaPatt chandec -> prPrec i 0 (concatD [prt 0 chandec])
    ParPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    TenPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    SeqPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print OptSession where
  prt i e = case e of
    NoSession -> prPrec i 0 (concatD [])
    SoSession rsession -> prPrec i 0 (concatD [doc (showString ":"), prt 0 rsession])

instance Print RSession where
  prt i e = case e of
    Repl term optrepl -> prPrec i 0 (concatD [prt 0 term, prt 0 optrepl])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print OptRepl where
  prt i e = case e of
    One -> prPrec i 0 (concatD [])
    Some aterm -> prPrec i 0 (concatD [doc (showString "^"), prt 0 aterm])

instance Print CSession where
  prt i e = case e of
    Cont term -> prPrec i 0 (concatD [doc (showString "."), prt 1 term])
    Done -> prPrec i 0 (concatD [])

instance Print AllocTerm where
  prt i e = case e of
    AVar name -> prPrec i 0 (concatD [prt 0 name])
    ALit literal -> prPrec i 0 (concatD [prt 0 literal])
    AParen term optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")")])
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])
instance Print NewPatt where
  prt i e = case e of
    TenNewPatt chandecs -> prPrec i 0 (concatD [doc (showString "["), prt 0 chandecs, doc (showString "]")])
    SeqNewPatt chandecs -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 chandecs, doc (showString ":]")])
    CntNewPatt name optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 optsig, doc (showString ")")])

instance Print NewAlloc where
  prt i e = case e of
    New newpatt -> prPrec i 0 (concatD [doc (showString "new"), prt 0 newpatt])
    NewSAnn term optsig newpatt -> prPrec i 0 (concatD [doc (showString "new/"), doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")"), prt 0 newpatt])
    NewNAnn opname allocterms newpatt -> prPrec i 0 (concatD [prt 0 opname, prt 0 allocterms, prt 0 newpatt])

instance Print a => Print (Scoped a) where
  prt i (Scoped _ ld x)
    -- the global scope is not displayed
    | nullDefs ld = prt i x
    | otherwise   =
        concatD [ doc (showString "let ") , prt 0 ld
                , doc (showString "in")
                , prt i x ]

instance Print N.Defs where
  prt _ = prtSeq id id (txt "⦃") (txt ",") (txt "⦄") . map prettyDef . m2l . N._defsMap
    where prettyDef (x, Ann mty tm) =
            prt 0 x .
            (case mty of
              Nothing -> id
              Just ty -> txt " : " . prt 0 ty) .
            txt " = " . prt 0 tm

instance Print N.Session where
  prt     i = prt i . reifySession
  prtList i = prtList i . reifySessions

instance Print N.Sessions where
  prt     i = prt i . view N._Sessions
  prtList i = prtList i . map (view N._Sessions)

instance Print N.RSession where
  prt     i = prt i . reifyRSession
  prtList i = prtList i . reifyRSessions

instance Print N.Act where
  prt     i = prt i . reifyAct
  prtList i = prtList i . map reifyAct

instance Print N.Proc where
  prt     i = prt i . reifyProc
  prtList i = prtList i . map reifyProc

instance Print N.Dec where
  prt     i = prt i . reifyDec
  prtList i = prtList i . map reifyDec

instance Print N.Program where
  prt     i = prt i . reifyProgram
  prtList i = prtList i . map reifyProgram

instance Print N.Term where
  prt     i = prt i . reifyTerm
  prtList i = prtList i . map reifyTerm

instance Print N.RFactor where
  prt     i (N.RFactor t) = prt i t
  prtList i = prtList i . map N._rterm

instance Print N.ChanDec where
  prt     i cd = prt i (reify cd :: ChanDec)
  prtList i cds = prtList i (map reify cds :: [ChanDec])

instance Print N.NewPatt where
  prt     i cd = prt i (reify cd :: NewPatt)
  prtList i cds = prtList i (map reify cds :: [NewPatt])

instance Print N.DefKind where
  prt     i = prt i . CN . Name . show
  prtList i = prtList i . map (CN . Name . show)
