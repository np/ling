-- File generated by the BNF Converter (bnfc 2.9.4.1).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for Ling.

{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-name-shadowing #-}
module Ling.Fmt.Benjamin.Print where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified Ling.Fmt.Benjamin.Abs

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Ling.Fmt.Benjamin.Abs.Name where
  prt _ (Ling.Fmt.Benjamin.Abs.Name i) = doc $ showString i
instance Print Ling.Fmt.Benjamin.Abs.OpName where
  prt _ (Ling.Fmt.Benjamin.Abs.OpName i) = doc $ showString i
instance Print Ling.Fmt.Benjamin.Abs.Program where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Prg decs -> prPrec i 0 (concatD [prt 0 decs])

instance Print Ling.Fmt.Benjamin.Abs.Dec where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.DDef name optsig term -> prPrec i 0 (concatD [prt 0 name, prt 0 optsig, doc (showString "="), prt 0 term])
    Ling.Fmt.Benjamin.Abs.DSig name term -> prPrec i 0 (concatD [prt 0 name, doc (showString ":"), prt 0 term])
    Ling.Fmt.Benjamin.Abs.DDat name connames -> prPrec i 0 (concatD [doc (showString "data"), prt 0 name, doc (showString "="), prt 0 connames])
    Ling.Fmt.Benjamin.Abs.DAsr assertion -> prPrec i 0 (concatD [doc (showString "assert"), prt 0 assertion])

instance Print Ling.Fmt.Benjamin.Abs.Assertion where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.AEq term1 term2 optsig -> prPrec i 0 (concatD [prt 0 term1, doc (showString "="), prt 0 term2, prt 0 optsig])

instance Print Ling.Fmt.Benjamin.Abs.ConName where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.CN name -> prPrec i 0 (concatD [doc (showString "`"), prt 0 name])

instance Print [Ling.Fmt.Benjamin.Abs.ConName] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString "|"), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.OptSig where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.NoSig -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.SoSig term -> prPrec i 0 (concatD [doc (showString ":"), prt 0 term])

instance Print [Ling.Fmt.Benjamin.Abs.Dec] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.VarDec where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.VD name optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 optsig, doc (showString ")")])

instance Print Ling.Fmt.Benjamin.Abs.ChanDec where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.CD name optrepl optsession -> prPrec i 0 (concatD [prt 0 name, prt 0 optrepl, prt 0 optsession])

instance Print [Ling.Fmt.Benjamin.Abs.ChanDec] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.Branch where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Br conname term -> prPrec i 0 (concatD [prt 0 conname, doc (showString "->"), prt 0 term])

instance Print [Ling.Fmt.Benjamin.Abs.Branch] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.Literal where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.LInteger n -> prPrec i 0 (concatD [prt 0 n])
    Ling.Fmt.Benjamin.Abs.LDouble d -> prPrec i 0 (concatD [prt 0 d])
    Ling.Fmt.Benjamin.Abs.LString str -> prPrec i 0 (concatD [printString str])
    Ling.Fmt.Benjamin.Abs.LChar c -> prPrec i 0 (concatD [prt 0 c])

instance Print Ling.Fmt.Benjamin.Abs.ATerm where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Var name -> prPrec i 0 (concatD [prt 0 name])
    Ling.Fmt.Benjamin.Abs.Op opname -> prPrec i 0 (concatD [prt 0 opname])
    Ling.Fmt.Benjamin.Abs.Lit literal -> prPrec i 0 (concatD [prt 0 literal])
    Ling.Fmt.Benjamin.Abs.Con conname -> prPrec i 0 (concatD [prt 0 conname])
    Ling.Fmt.Benjamin.Abs.TTyp -> prPrec i 0 (concatD [doc (showString "Type")])
    Ling.Fmt.Benjamin.Abs.TProto rsessions -> prPrec i 0 (concatD [doc (showString "<"), prt 0 rsessions, doc (showString ">")])
    Ling.Fmt.Benjamin.Abs.Paren term optsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")")])
    Ling.Fmt.Benjamin.Abs.End -> prPrec i 0 (concatD [doc (showString "end")])
    Ling.Fmt.Benjamin.Abs.Par rsessions -> prPrec i 0 (concatD [doc (showString "{"), prt 0 rsessions, doc (showString "}")])
    Ling.Fmt.Benjamin.Abs.Ten rsessions -> prPrec i 0 (concatD [doc (showString "["), prt 0 rsessions, doc (showString "]")])
    Ling.Fmt.Benjamin.Abs.Seq rsessions -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 rsessions, doc (showString ":]")])

instance Print [Ling.Fmt.Benjamin.Abs.ATerm] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.Term where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.RawApp aterm aterms -> prPrec i 3 (concatD [prt 0 aterm, prt 0 aterms])
    Ling.Fmt.Benjamin.Abs.Case term branchs -> prPrec i 2 (concatD [doc (showString "case"), prt 0 term, doc (showString "of"), doc (showString "{"), prt 0 branchs, doc (showString "}")])
    Ling.Fmt.Benjamin.Abs.Snd term csession -> prPrec i 2 (concatD [doc (showString "!"), prt 3 term, prt 0 csession])
    Ling.Fmt.Benjamin.Abs.Rcv term csession -> prPrec i 2 (concatD [doc (showString "?"), prt 3 term, prt 0 csession])
    Ling.Fmt.Benjamin.Abs.Dual term -> prPrec i 2 (concatD [doc (showString "~"), prt 2 term])
    Ling.Fmt.Benjamin.Abs.TRecv name -> prPrec i 2 (concatD [doc (showString "<-"), prt 0 name])
    Ling.Fmt.Benjamin.Abs.Loli term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "-o"), prt 1 term2])
    Ling.Fmt.Benjamin.Abs.TFun term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "->"), prt 1 term2])
    Ling.Fmt.Benjamin.Abs.TSig term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "**"), prt 1 term2])
    Ling.Fmt.Benjamin.Abs.Let name optsig term1 term2 -> prPrec i 1 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 term1, doc (showString "in"), prt 0 term2])
    Ling.Fmt.Benjamin.Abs.Lam term1 term2 -> prPrec i 0 (concatD [doc (showString "\\"), prt 2 term1, doc (showString "->"), prt 0 term2])
    Ling.Fmt.Benjamin.Abs.TProc chandecs proc_ -> prPrec i 0 (concatD [doc (showString "proc"), doc (showString "("), prt 0 chandecs, doc (showString ")"), prt 0 proc_])

instance Print Ling.Fmt.Benjamin.Abs.Proc where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.PAct act -> prPrec i 1 (concatD [prt 0 act])
    Ling.Fmt.Benjamin.Abs.PPrll procs -> prPrec i 1 (concatD [doc (showString "("), prt 0 procs, doc (showString ")")])
    Ling.Fmt.Benjamin.Abs.PRepl replkind aterm withindex proc_ -> prPrec i 1 (concatD [prt 0 replkind, doc (showString "^"), prt 0 aterm, prt 0 withindex, prt 1 proc_])
    Ling.Fmt.Benjamin.Abs.PNxt proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, prt 0 proc_2])
    Ling.Fmt.Benjamin.Abs.PDot proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, doc (showString "."), prt 0 proc_2])
    Ling.Fmt.Benjamin.Abs.PSem proc_1 proc_2 -> prPrec i 0 (concatD [prt 1 proc_1, doc (showString ";"), prt 0 proc_2])
    Ling.Fmt.Benjamin.Abs.NewSlice chandecs aterm name proc_ -> prPrec i 0 (concatD [doc (showString "slice"), doc (showString "("), prt 0 chandecs, doc (showString ")"), prt 0 aterm, doc (showString "as"), prt 0 name, prt 0 proc_])

instance Print [Ling.Fmt.Benjamin.Abs.Proc] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString "|"), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.ReplKind where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.ReplSeq -> prPrec i 0 (concatD [doc (showString "sequence")])
    Ling.Fmt.Benjamin.Abs.ReplPar -> prPrec i 0 (concatD [doc (showString "parallel")])

instance Print Ling.Fmt.Benjamin.Abs.WithIndex where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.NoIndex -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.SoIndex name -> prPrec i 0 (concatD [doc (showString "with"), prt 0 name])

instance Print Ling.Fmt.Benjamin.Abs.Act where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Nu newalloc -> prPrec i 0 (concatD [prt 0 newalloc])
    Ling.Fmt.Benjamin.Abs.ParSplit optsplit chandecs -> prPrec i 0 (concatD [prt 0 optsplit, doc (showString "{"), prt 0 chandecs, doc (showString "}")])
    Ling.Fmt.Benjamin.Abs.TenSplit optsplit chandecs -> prPrec i 0 (concatD [prt 0 optsplit, doc (showString "["), prt 0 chandecs, doc (showString "]")])
    Ling.Fmt.Benjamin.Abs.SeqSplit optsplit chandecs -> prPrec i 0 (concatD [prt 0 optsplit, doc (showString "[:"), prt 0 chandecs, doc (showString ":]")])
    Ling.Fmt.Benjamin.Abs.Send name aterm -> prPrec i 0 (concatD [doc (showString "send"), prt 0 name, prt 0 aterm])
    Ling.Fmt.Benjamin.Abs.NewSend name optsession aterm -> prPrec i 0 (concatD [prt 0 name, prt 0 optsession, doc (showString "<-"), prt 0 aterm])
    Ling.Fmt.Benjamin.Abs.Recv name vardec -> prPrec i 0 (concatD [doc (showString "recv"), prt 0 name, prt 0 vardec])
    Ling.Fmt.Benjamin.Abs.NewRecv name1 optsig name2 -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name1, prt 0 optsig, doc (showString "<-"), prt 0 name2])
    Ling.Fmt.Benjamin.Abs.LetRecv name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "<="), prt 0 aterm])
    Ling.Fmt.Benjamin.Abs.Ax asession chandecs -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 asession, doc (showString "("), prt 0 chandecs, doc (showString ")")])
    Ling.Fmt.Benjamin.Abs.SplitAx n asession name -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 n, prt 0 asession, prt 0 name])
    Ling.Fmt.Benjamin.Abs.At aterm topcpatt -> prPrec i 0 (concatD [doc (showString "@"), prt 0 aterm, prt 0 topcpatt])
    Ling.Fmt.Benjamin.Abs.LetA name optsig aterm -> prPrec i 0 (concatD [doc (showString "let"), prt 0 name, prt 0 optsig, doc (showString "="), prt 0 aterm])

instance Print Ling.Fmt.Benjamin.Abs.ASession where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.AS aterm -> prPrec i 0 (concatD [prt 0 aterm])

instance Print Ling.Fmt.Benjamin.Abs.OptAs where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.NoAs -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.SoAs -> prPrec i 0 (concatD [doc (showString "as")])

instance Print Ling.Fmt.Benjamin.Abs.OptSplit where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.SoSplit name optas -> prPrec i 0 (concatD [doc (showString "split"), prt 0 name, prt 0 optas])
    Ling.Fmt.Benjamin.Abs.NoSplit name -> prPrec i 0 (concatD [prt 0 name])

instance Print Ling.Fmt.Benjamin.Abs.TopCPatt where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.OldTopPatt chandecs -> prPrec i 0 (concatD [doc (showString "("), prt 0 chandecs, doc (showString ")")])
    Ling.Fmt.Benjamin.Abs.ParTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    Ling.Fmt.Benjamin.Abs.TenTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Fmt.Benjamin.Abs.SeqTopPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])

instance Print Ling.Fmt.Benjamin.Abs.CPatt where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.ChaPatt chandec -> prPrec i 0 (concatD [prt 0 chandec])
    Ling.Fmt.Benjamin.Abs.ParPatt cpatts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 cpatts, doc (showString "}")])
    Ling.Fmt.Benjamin.Abs.TenPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Fmt.Benjamin.Abs.SeqPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])

instance Print [Ling.Fmt.Benjamin.Abs.CPatt] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.OptSession where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.NoSession -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.SoSession rsession -> prPrec i 0 (concatD [doc (showString ":"), prt 0 rsession])

instance Print Ling.Fmt.Benjamin.Abs.RSession where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Repl term optrepl -> prPrec i 0 (concatD [prt 0 term, prt 0 optrepl])

instance Print [Ling.Fmt.Benjamin.Abs.RSession] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.OptRepl where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.One -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.Some aterm -> prPrec i 0 (concatD [doc (showString "^"), prt 0 aterm])

instance Print Ling.Fmt.Benjamin.Abs.CSession where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.Cont term -> prPrec i 0 (concatD [doc (showString "."), prt 1 term])
    Ling.Fmt.Benjamin.Abs.Done -> prPrec i 0 (concatD [])

instance Print Ling.Fmt.Benjamin.Abs.AllocTerm where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.AVar name -> prPrec i 0 (concatD [prt 0 name])
    Ling.Fmt.Benjamin.Abs.ALit literal -> prPrec i 0 (concatD [prt 0 literal])

instance Print [Ling.Fmt.Benjamin.Abs.AllocTerm] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print Ling.Fmt.Benjamin.Abs.NewSig where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.NoNewSig -> prPrec i 0 (concatD [])
    Ling.Fmt.Benjamin.Abs.NewTypeSig term -> prPrec i 0 (concatD [doc (showString ":*"), prt 0 term])
    Ling.Fmt.Benjamin.Abs.NewSessSig term -> prPrec i 0 (concatD [doc (showString ":"), prt 0 term])

instance Print Ling.Fmt.Benjamin.Abs.NewPatt where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.TenNewPatt cpatts -> prPrec i 0 (concatD [doc (showString "["), prt 0 cpatts, doc (showString "]")])
    Ling.Fmt.Benjamin.Abs.SeqNewPatt cpatts -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 cpatts, doc (showString ":]")])
    Ling.Fmt.Benjamin.Abs.CntNewPatt name newsig -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, prt 0 newsig, doc (showString ")")])

instance Print Ling.Fmt.Benjamin.Abs.NewAlloc where
  prt i = \case
    Ling.Fmt.Benjamin.Abs.OldNew chandecs -> prPrec i 0 (concatD [doc (showString "new"), doc (showString "("), prt 0 chandecs, doc (showString ")")])
    Ling.Fmt.Benjamin.Abs.New newpatt -> prPrec i 0 (concatD [doc (showString "new"), prt 0 newpatt])
    Ling.Fmt.Benjamin.Abs.NewSAnn term optsig newpatt -> prPrec i 0 (concatD [doc (showString "new/"), doc (showString "("), prt 0 term, prt 0 optsig, doc (showString ")"), prt 0 newpatt])
    Ling.Fmt.Benjamin.Abs.NewNAnn opname allocterms newpatt -> prPrec i 0 (concatD [prt 0 opname, prt 0 allocterms, prt 0 newpatt])
