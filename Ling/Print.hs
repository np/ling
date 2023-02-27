{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- See Ling.Print.Class about how this module has been changed
module Ling.Print (module Ling.Print.Class) where

import qualified Ling.Abs
import qualified Ling.Norm as N
import           Ling.Prelude
import           Ling.Print.Class
import           Ling.Reify
import           Ling.Scoped


instance Print Ling.Abs.NewName where
  prt _ (Ling.Abs.NewName i) = doc $ showString i
instance Print Ling.Abs.OpName where
  prt _ (Ling.Abs.OpName i) = doc $ showString i
instance Print Ling.Abs.Program where
  prt i = \case
    Ling.Abs.Prg decs -> prPrec i 0 (concatD [prt 0 decs])

instance Print Ling.Abs.Dec where
  prt i = \case
    Ling.Abs.DDef name optsig term -> prPrec i 0 (concatD [prt 0 name, prt 0 optsig, txt "=\n", prt 0 term]) -- NP: newline
    Ling.Abs.DSig name term -> prPrec i 0 (concatD [prt 0 name, txt ": ", prt 0 term]) -- NP: space
    Ling.Abs.DDat name connames -> prPrec i 0 (concatD [doc (showString "data"), prt 0 name, doc (showString "="), prt 0 connames])
    Ling.Abs.DAsr assertion -> prPrec i 0 (concatD [txt "assert", txt "+\n", prt 0 assertion, txt "-\n"]) -- NP: newlines

instance Print Ling.Abs.Assertion where
  prt i = \case
    Ling.Abs.AEq term1 term2 optsig -> prPrec i 0 (concatD [prt 0 term1, nl, txt "=\n", prt 0 term2, nl, prt 0 optsig]) -- NP: 3 newlines

instance Print Ling.Abs.ConName where
  prt i = \case
    Ling.Abs.CN name -> prPrec i 0 (concatD [doc (showString "`"), prt 0 name])

instance Print [Ling.Abs.ConName] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString "|"), prt 0 xs]

instance Print Ling.Abs.OptSig where
  prt i = \case
    Ling.Abs.NoSig -> prPrec i 0 (concatD [])
    Ling.Abs.SoSig term -> prPrec i 0 (concatD [txt ": ", prt 0 term]) -- NP: space

instance Print [Ling.Abs.Dec] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, txt ",\n\n", prt 0 xs] -- NP: added newlines

instance Print Ling.Abs.VarDec where
  prt i = \case
    Ling.Abs.VD name optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 optsig, doc (showString ")")])

instance Print Ling.Abs.ChanDec where
  prt i = \case
    Ling.Abs.CD name optrepl optsession -> prPrec i 0 (concatD [prt 0 name, prt 0 optrepl, prt 0 optsession])

instance Print [Ling.Abs.ChanDec] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Abs.Branch where
  prt i = \case
    Ling.Abs.Br conname term -> prPrec i 0 (concatD [prt 0 conname, doc (showString "->"), prt 0 term])

instance Print [Ling.Abs.Branch] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, txt ",\n", prt 0 xs] -- NP: newline

instance Print Ling.Abs.Literal where
  prt i = \case
    Ling.Abs.LInteger n -> prPrec i 0 (concatD [prt 0 n])
    Ling.Abs.LDouble d -> prPrec i 0 (concatD [prt 0 d])
    Ling.Abs.LString str -> prPrec i 0 (concatD [printString str])
    Ling.Abs.LChar c -> prPrec i 0 (concatD [prt 0 c])

instance Print Ling.Abs.ATerm where
  prt i = \case
    Ling.Abs.Var name -> prPrec i 0 (concatD [prt 0 name])
    Ling.Abs.Op opname -> prPrec i 0 (concatD [prt 0 opname])
    Ling.Abs.Lit literal -> prPrec i 0 (concatD [prt 0 literal])
    Ling.Abs.Con conname -> prPrec i 0 (concatD [prt 0 conname])
    Ling.Abs.TTyp -> prPrec i 0 (concatD [doc (showString "Type")])
    Ling.Abs.TProto rsessions -> prPrec i 0 (concatD [doc (showString "<"), prt 0 rsessions, doc (showString ">")])
    Ling.Abs.Paren term optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")")])
    Ling.Abs.End -> prPrec i 0 (concatD [doc (showString "end")])
    Ling.Abs.Par rsessions -> prPrec i 0 (concatD [doc (showString "{"), prt 0 rsessions, doc (showString "}")])
    Ling.Abs.Ten rsessions -> prPrec i 0 (concatD [doc (showString "["), prt 0 rsessions, doc (showString "]")])
    Ling.Abs.Seq rsessions -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 rsessions, doc (showString ":]")])

instance Print [Ling.Abs.ATerm] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print Ling.Abs.Term where
  prt i = \case
    Ling.Abs.RawApp aterm aterms -> prPrec i 3 (concatD [prt 0 aterm, prt 0 aterms])
    Ling.Abs.Case term branchs -> prPrec i 2 (concatD [txt "case", prt 0 term, txt "of", txt "{\n", prt 0 branchs, txt "\n}"]) -- NP: newlines
    Ling.Abs.Snd term csession -> prPrec i 2 (concatD [doc (showString "!"), prt 3 term, prt 0 csession])
    Ling.Abs.Rcv term csession -> prPrec i 2 (concatD [doc (showString "?"), prt 3 term, prt 0 csession])
    Ling.Abs.Dual term -> prPrec i 2 (concatD [doc (showString "~"), prt 2 term])
    Ling.Abs.TRecv name -> prPrec i 2 (concatD [doc (showString "<-"), prt 0 name])
    Ling.Abs.Loli term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "-o"), prt 1 term2])
    Ling.Abs.TFun term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "->"), prt 1 term2])
    Ling.Abs.TSig term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "**"), prt 1 term2])
    Ling.Abs.Let name optsig term1 term2 -> prPrec i 1 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 term1, txt "in\n", prt 0 term2]) -- NP: newline
    Ling.Abs.Lam term1 term2 -> prPrec i 0 (concatD [doc (showString "\\"), prt 2 term1, doc (showString "->"), prt 0 term2])
    Ling.Abs.TProc chandecs proc_ -> prPrec i 0 (concatD [txt "proc", txt "(", prt 0 chandecs, txt ")", nl, prt 0 proc_]) -- NP: newline

instance Print Ling.Abs.Proc where
  prt i = \case
    Ling.Abs.PAct act -> prPrec i 1 (concatD [prt 0 act])
    Ling.Abs.PPrll procs -> prPrec i 1 (concatD [txt "(\n", prt 0 procs, txt "\n)"]) -- NP: newlines
    Ling.Abs.PRepl replkind aterm withindex proc_ -> prPrec i 0 (concatD [prt 0 replkind, doc (showString "^"), prt 0 aterm, prt 0 withindex, txt "+\n", prt 1 proc_, txt "-\n"]) -- NP: newlines
    Ling.Abs.PNxt proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, nl, prt 0 proc_2]) -- NP: newline
    Ling.Abs.PDot proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, doc (showString ".\n"), prt 0 proc_2]) -- NP: newline
    Ling.Abs.PSem proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, doc (showString ";\n"), prt 0 proc_2]) -- NP: newline

instance Print [Ling.Abs.Proc] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, txt "\n|", prt 0 xs] -- NP: newline

instance Print Ling.Abs.ReplKind where
  prt i = \case
    Ling.Abs.ReplSeq -> prPrec i 0 (concatD [doc (showString "sequence")])
    Ling.Abs.ReplPar -> prPrec i 0 (concatD [doc (showString "parallel")])

instance Print Ling.Abs.WithIndex where
  prt i = \case
    Ling.Abs.NoIndex -> prPrec i 0 (concatD [])
    Ling.Abs.SoIndex name -> prPrec i 0 (concatD [doc (showString "with"), prt 0 name])

instance Print Ling.Abs.Act where
  prt i = \case
    Ling.Abs.Nu newalloc -> prPrec i 0 (concatD [prt 0 newalloc])
    Ling.Abs.Split split -> prPrec i 0 (concatD [prt 0 split])
    Ling.Abs.Send name aterm -> prPrec i 0 (concatD [doc (showString "send"), prt 0 name, prt 0 aterm])
    Ling.Abs.NewSend name optsession aterm -> prPrec i 0 (concatD [prt 0 name, prt 0 optsession, doc (showString "<-"), prt 0 aterm])
    Ling.Abs.Recv name vardec -> prPrec i 0 (concatD [doc (showString "recv"), prt 0 name, prt 0 vardec])
    Ling.Abs.NewRecv name1 optsig name2 -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name1, prt 0 optsig, doc (showString "<-"), prt 0 name2])
    Ling.Abs.LetRecv name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "<="), prt 0 aterm])
    Ling.Abs.Ax asession chandecs -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 asession, doc (showString "("), prt 0 chandecs, doc (showString ")")])
    Ling.Abs.SplitAx n asession name -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 n, prt 0 asession, prt 0 name])
    Ling.Abs.At aterm topcpatt -> prPrec i 0 (concatD [doc (showString "@"), prt 0 aterm, prt 0 topcpatt])
    Ling.Abs.LetA name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 aterm])

instance Print Ling.Abs.ASession where
  prt i = \case
    Ling.Abs.AS aterm -> prPrec i 0 (concatD [prt 0 aterm])

instance Print Ling.Abs.Split where
  prt i = \case
    Ling.Abs.PatSplit name optas cpatt -> prPrec i 0 (concatD [doc (showString "split"), prt 0 name, prt 0 optas, prt 0 cpatt])
    Ling.Abs.ParSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "{"), prt 0 chandecs, doc (showString "}")])
    Ling.Abs.TenSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "["), prt 0 chandecs, doc (showString "]")])
    Ling.Abs.SeqSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "[:"), prt 0 chandecs, doc (showString ":]")])

instance Print Ling.Abs.OptAs where
  prt i = \case
    Ling.Abs.NoAs -> prPrec i 0 (concatD [])
    Ling.Abs.SoAs -> prPrec i 0 (concatD [doc (showString "as")])

instance Print Ling.Abs.TopCPatt where
  prt i = \case
    Ling.Abs.OldTopPatt chandecs -> prPrec i 0 (concatD [doc (showString "("), prt 0 chandecs, doc (showString ")")])
    Ling.Abs.ParTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    Ling.Abs.TenTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Abs.SeqTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])

instance Print Ling.Abs.CPatt where
  prt i = \case
    Ling.Abs.ChaPatt chandec -> prPrec i 0 (concatD [prt 0 chandec])
    Ling.Abs.ParPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    Ling.Abs.TenPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Abs.SeqPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])

instance Print [Ling.Abs.CPatt] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Abs.OptSession where
  prt i = \case
    Ling.Abs.NoSession -> prPrec i 0 (concatD [])
    Ling.Abs.SoSession rsession -> prPrec i 0 (concatD [doc (showString ":"), prt 0 rsession])

instance Print Ling.Abs.RSession where
  prt i = \case
    Ling.Abs.Repl term optrepl -> prPrec i 0 (concatD [prt 0 term, prt 0 optrepl])

instance Print [Ling.Abs.RSession] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Abs.OptRepl where
  prt i = \case
    Ling.Abs.One -> prPrec i 0 (concatD [])
    Ling.Abs.Some aterm -> prPrec i 0 (concatD [doc (showString "^"), prt 0 aterm])

instance Print Ling.Abs.CSession where
  prt i = \case
    Ling.Abs.Cont term -> prPrec i 0 (concatD [doc (showString "."), prt 1 term])
    Ling.Abs.Done -> prPrec i 0 (concatD [])

instance Print Ling.Abs.NewSig where
  prt i = \case
    Ling.Abs.NoNewSig -> prPrec i 0 (concatD [])
    Ling.Abs.NewTypeSig term -> prPrec i 0 (concatD [doc (showString ":*"), prt 0 term])
    Ling.Abs.NewSessSig term -> prPrec i 0 (concatD [doc (showString ":"), prt 0 term])

instance Print Ling.Abs.NewPatt where
  prt i = \case
    Ling.Abs.TenNewPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Abs.SeqNewPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])
    Ling.Abs.CntNewPatt name newsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 newsig, doc (showString ")")])

instance Print Ling.Abs.NewAlloc where
  prt i = \case
    Ling.Abs.New newpatt -> prPrec i 0 (concatD [doc (showString "new"), prt 0 newpatt])
    Ling.Abs.NewSAnn term optsig newpatt -> prPrec i 0 (concatD [txt "new/(", prt 0 term, prt 0 optsig, doc (showString ")"), prt 0 newpatt]) -- NP: avoids a space after "new/"
    Ling.Abs.NewNAnn newname newpatt -> prPrec i 0 (concatD [prt 0 newname, prt 0 newpatt])

instance Print a => Print (Scoped a) where
  prt i (Scoped _ ld x)
    -- the global scope is not displayed
    | nullDefs ld = prt i x
    | otherwise   =
        concatD [ doc (showString "let ") , prt 0 ld
                , doc (showString "in\n")
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
--  prtList i = prtList i . reifySessions

instance Print N.Sessions where
  prt     i = prt i . view N._Sessions
--  prtList i = prtList i . map (view N._Sessions)

instance Print N.RSession where
  prt     i = prt i . reifyRSession

instance Print [N.RSession] where
  prt i = prt i . reifyRSessions

instance Print N.Act where
  prt     i = prt i . reifyAct
--  prtList i = prtList i . map reifyAct

instance Print N.Proc where
  prt     i = prt i . reifyProc

instance Print [N.Proc] where
  prt i = prt i . map reifyProc

instance Print N.Dec where
  prt     i = prt i . reifyDec
--  prtList i = prtList i . map reifyDec

instance Print N.Program where
  prt     i = prt i . reifyProgram
--  prtList i = prtList i . map reifyProgram

instance Print N.Term where
  prt     i = prt i . reifyTerm
--  prtList i = prtList i . map reifyTerm

instance Print N.RFactor where
  prt     i (N.RFactor t) = prt i t
--  prtList i = prtList i . map N._rterm

instance Print N.ChanDec where
  prt     i cd = prt i (reify cd :: Ling.Abs.ChanDec)
 -- prtList i cds = prtList i (map reify cds :: [Ling.Abs.ChanDec])

instance Print N.CPatt where
  prt     i cd = prt i (reify cd :: Ling.Abs.CPatt)
--  prtList i cds = prtList i (map reify cds :: [Ling.Abs.CPatt])

instance Print N.NewPatt where
  prt     i cd = prt i (reify cd :: Ling.Abs.NewPatt)
--  prtList i cds = prtList i (map reify cds :: [Ling.Abs.NewPatt])

instance Print N.DefKind where
  prt     i = prt i . Ling.Abs.CN . Ling.Abs.Name . show
--  prtList i = prtList i . map (Ling.Abs.CN . Ling.Abs.Name . show)
