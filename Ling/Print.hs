{-# LANGUAGE LambdaCase #-}
module Ling.Print where

-- pretty-printer generated by the BNF converter
-- and modified thereafter. After running bnfc you
-- merge the changes using:
--   git checkout -p Ling/Print.hs
-- You can then select y(es) for the hunks to revert
-- and n(o) for the ones you want to keep.

import           Data.Char
import           Data.Map    (Map)
import           Data.Set    (Set)
import           Debug.Trace
import           Ling.Abs
import           Ling.ErrM
import qualified Ling.Norm as N
import           Ling.Reify
import           Ling.Scoped
import           Ling.Utils hiding (q)


-- the top-level printing method
pretty :: Print a => a -> String
pretty = render . prt 0

tracePretty :: Print a => String -> a -> a
tracePretty msg x = trace (msg ++ " " ++ pretty x) x

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "\n"        :ts -> new i . rend i ts
    [c]         :ts | c `elem` "{[(.?!`" -> showChar c . dropWhile isSpace . rend i ts
    ": "        :ts -> space ":" . rend (i+1) ts
    "=\n"       :ts -> showString "=" . new 1 . rend 1 ts
    [c,'\n']    :ts | c `elem` "{[" -> showChar c . new (i+1) . rend (i+1) ts
    [c,'\n']    :ts | c `elem` "("  -> space [c] . rend (i+1) ts
    ['\n',c]:",":ts | c `elem` "}]" -> new (i-1) . showChar c . new (i-1) . rend (i-1) ts
    ['\n',c]    :ts | c `elem` "}]" -> new (i-1) . space [c] . rend (i-1) ts
    ['\n',c]    :ts | c `elem` ")"  -> {-unlessElem " " (showChar ' ') .-} showChar c . rend (i-1) ts
    ",\n\n"     :ts -> new 0 . new 0 . rend 0 ts
    [c,'\n']    :ts | c `elem` ",."  -> showChar c . new i . rend i ts
    ['\n',c]    :ts | c `elem` "|X⁇"  -> new (i-1) . space [c] . rend i ts
    t:","       :ts -> showString t . space "," . rend i ts
    ","         :ts -> showChar ',' . rend i ts
    t  : [c]    :ts | c `elem` "}])" -> showString t . showChar c . rend i ts
    t           :ts -> space t . rend i ts
    _            -> id
  new    i = showChar '\n' . indent i
  indent i = unlessElem "\n" (replicateS (2*i) (showChar ' '))
  space  t = showString t . unlessElem ".\n" (showChar ' ')
  unlessElem set f s
    | null s || head s `elem` set = s
    | otherwise                   = f s

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- the printer class does the job
class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j<i then parenth else id


instance Print Integer where
  prt _ x = doc (shows x)


instance Print Double where
  prt _ x = doc (shows x)



instance Print Name where
  prt _ (Name i) = doc (showString ( i))
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])


instance Print Program where
  prt i e = case e of
    Prg decs -> prPrec i 0 (concatD [prt 0 decs])

instance Print Dec where
  prt i e = case e of
    DDef name optsig term -> prPrec i 0 (concatD [prt 0 name, prt 0 optsig, doc (showString "=\n"), prt 0 term])
    DSig name term -> prPrec i 0 (concatD [prt 0 name, doc (showString ": "), prt 0 term])
    DDat name connames -> prPrec i 0 (concatD [doc (showString "data"), prt 0 name, doc (showString "="), prt 0 connames])
    DAsr assertion -> prPrec i 0 (concatD [doc (showString "assert"), prt 0 assertion])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ",\n\n"), prt 0 xs])
instance Print Assertion where
  prt i e = case e of
    AEq term1 term2 term3 -> prPrec i 0 (concatD [prt 0 term1, doc (showString "="), prt 0 term2, doc (showString ":"), prt 0 term3])

instance Print ConName where
  prt i e = case e of
    CN name -> prPrec i 0 (concatD [doc (showString "`"), prt 0 name])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString "|"), prt 0 xs])
instance Print OptSig where
  prt i e = case e of
    NoSig -> prPrec i 0 (concatD [])
    SoSig term -> prPrec i 0 (concatD [doc (showString ": "), prt 0 term])

instance Print VarDec where
  prt i e = case e of
    VD name term -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, doc (showString ":"), prt 0 term, doc (showString ")")])

instance Print VarsDec where
  prt i e = case e of
    VsD aterm aterms term -> prPrec i 0 (concatD [doc (showString "("), prt 0 aterm, prt 0 aterms, doc (showString ":"), prt 0 term, doc (showString ")")])
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])
instance Print ChanDec where
  prt i e = case e of
    CD name optsession -> prPrec i 0 (concatD [prt 0 name, prt 0 optsession])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ","), prt 0 xs])
instance Print Branch where
  prt i e = case e of
    Br conname term -> prPrec i 0 (concatD [prt 0 conname, doc (showString "->"), prt 0 term])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString ",\n"), prt 0 xs])
instance Print Literal where
  prt i e = case e of
    LInteger n -> prPrec i 0 (concatD [prt 0 n])
    LDouble d -> prPrec i 0 (concatD [prt 0 d])
    LString str -> prPrec i 0 (concatD [prt 0 str])
    LChar c -> prPrec i 0 (concatD [prt 0 c])

instance Print ATerm where
  prt i e = case e of
    Var name -> prPrec i 0 (concatD [prt 0 name])
    Lit literal -> prPrec i 0 (concatD [prt 0 literal])
    Con conname -> prPrec i 0 (concatD [prt 0 conname])
    TTyp -> prPrec i 0 (concatD [doc (showString "Type")])
    TProto rsessions -> prPrec i 0 (concatD [doc (showString "<"), prt 0 rsessions, doc (showString ">")])
    Paren term -> prPrec i 0 (concatD [doc (showString "("), prt 0 term, doc (showString ")")])
    End -> prPrec i 0 (concatD [doc (showString "end")])
    Par rsessions -> prPrec i 0 (concatD [doc (showString "{"), prt 0 rsessions, doc (showString "}")])
    Ten rsessions -> prPrec i 0 (concatD [doc (showString "["), prt 0 rsessions, doc (showString "]")])
    Seq rsessions -> prPrec i 0 (concatD [doc (showString "[:"), prt 0 rsessions, doc (showString ":]")])
  prtList _ [] = (concatD [])
  prtList _ (x:xs) = (concatD [prt 0 x, prt 0 xs])
instance Print DTerm where
  prt i e = case e of
    DTTyp name aterms -> prPrec i 0 (concatD [prt 0 name, prt 0 aterms])
    DTBnd name term -> prPrec i 0 (concatD [doc (showString "("), prt 0 name, doc (showString ":"), prt 0 term, doc (showString ")")])

instance Print Term where
  prt i e = case e of
    RawApp aterm aterms -> prPrec i 2 (concatD [prt 0 aterm, prt 0 aterms])
    Case term branchs -> prPrec i 2 (concatD [doc (showString "case"), prt 0 term, doc (showString "of"), doc (showString "{\n"), prt 0 branchs, doc (showString "\n}")])
    Snd dterm csession -> prPrec i 2 (concatD [doc (showString "!"), prt 0 dterm, prt 0 csession])
    Rcv dterm csession -> prPrec i 2 (concatD [doc (showString "?"), prt 0 dterm, prt 0 csession])
    Dual term -> prPrec i 2 (concatD [doc (showString "~"), prt 2 term])
    Loli term1 term2 -> prPrec i 1 (concatD [prt 2 term1, doc (showString "-o"), prt 1 term2])
    TFun varsdec varsdecs term -> prPrec i 0 (concatD [prt 0 varsdec, prt 0 varsdecs, doc (showString "->"), prt 0 term])
    TSig varsdec varsdecs term -> prPrec i 0 (concatD [prt 0 varsdec, prt 0 varsdecs, doc (showString "**"), prt 0 term])
    Lam varsdec varsdecs term -> prPrec i 0 (concatD [doc (showString "\\"), prt 0 varsdec, prt 0 varsdecs, doc (showString "->"), prt 0 term])
    TProc chandecs proc -> prPrec i 0 (concatD [doc (showString "proc"), doc (showString "("), prt 0 chandecs, doc (showString ")"), nl, prt 0 proc])

instance Print Proc where
  prt i e = case e of
    PAct act -> prPrec i 1 (concatD [prt 0 act])
    PPrll procs -> prPrec i 1 (concatD [doc (showString "(\n"), prt 0 procs, doc (showString "\n)")])
    PNxt proc1 proc2 -> prPrec i 0 (concatD [prt 1 proc1, doc (showString "\n"), prt 0 proc2])
    PDot proc1 proc2 -> prPrec i 0 (concatD [prt 1 proc1, doc (showString ".\n"), prt 0 proc2])
  prtList _ [] = (concatD [])
  prtList _ [x] = (concatD [prt 0 x])
  prtList _ (x:xs) = (concatD [prt 0 x, doc (showString "\n|"), prt 0 xs])
instance Print Act where
  prt i e = case e of
    Nu chandec1 chandec2 -> prPrec i 0 (concatD [doc (showString "new"), doc (showString "("), prt 0 chandec1, doc (showString ","), prt 0 chandec2, doc (showString ")")])
    ParSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "{"), prt 0 chandecs, doc (showString "}")])
    TenSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "["), prt 0 chandecs, doc (showString "]")])
    SeqSplit name chandecs -> prPrec i 0 (concatD [prt 0 name, doc (showString "[:"), prt 0 chandecs, doc (showString ":]")])
    Send name aterm -> prPrec i 0 (concatD [doc (showString "send"), prt 0 name, prt 0 aterm])
    Recv name vardec -> prPrec i 0 (concatD [doc (showString "recv"), prt 0 name, prt 0 vardec])
    NewSlice chandecs aterm name -> prPrec i 0 (concatD [doc (showString "slice"), doc (showString "("), prt 0 chandecs, doc (showString ")"), prt 0 aterm, doc (showString "as"), prt 0 name])
    Ax asession chandecs -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 asession, doc (showString "("), prt 0 chandecs, doc (showString ")")])
    SplitAx n asession name -> prPrec i 0 (concatD [doc (showString "fwd"), prt 0 n, prt 0 asession, prt 0 name])
    At aterm topcpatt -> prPrec i 0 (concatD [doc (showString "@"), prt 0 aterm, prt 0 topcpatt])

instance Print ASession where
  prt i e = case e of
    AS aterm -> prPrec i 0 (concatD [prt 0 aterm])

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

txt :: String -> Doc
txt = doc . showString

nl :: Doc
nl = txt "\n"

instance Print a => Print (Maybe a) where
  prt i = \case
    Nothing -> txt "Nothing"
    Just x  -> prPrec i 0 (txt "Just" . prt 0 x)

prtSeq :: Doc -> Doc -> Doc -> Doc -> Doc -> [Doc] -> Doc
prtSeq n p b s e = \case
  []     -> concatD [p, b, e]
  [x]    -> concatD [p, b, x, e]
  (x:xs) -> concatD $ [n, p, b, x]
                   ++ [z | y <- xs, z <- [n, p, s, y]]
                   ++ [n, p, e]

instance (Ord a, Print a) => Print (Set a) where
--prt _i = prtSeq nl id (txt "⦃") (txt ",") (txt "⦄") . map (prt 0) . s2l
  prt _i = prtSeq id id (txt "⦃") (txt ",") (txt "⦄") . map (prt 0) . s2l

instance (Ord k, Print k, Print v) => Print (Map k v) where
--prt _i = prtSeq nl (txt "  ") (txt "⦃") (txt ",") (txt "⦄") . map prettyKV . m2l
  prt _i = prtSeq id id (txt "⦃") (txt ",") (txt "⦄") . map prettyKV . m2l
    where prettyKV (k,v) = prt 0 k . txt " ↦ " . prt 0 v

newtype Lst a = Lst { _unLst :: [a] }

instance Print a => Print (Lst a) where
  prt _i = prtSeq id id (txt "[") (txt ",") (txt "]") . map (prt 0) . _unLst

newtype Prll a = Prll { _unPrll :: [a] }

instance Print a => Print (Prll a) where
  prt _i = prtSeq id id (txt "(") (txt "|") (txt ")") . map (prt 0) . _unPrll

newtype Order a = Order { _unOrder :: [a] }

instance Print a => Print (Order a) where
  prt _i = prtSeq id id id (txt ".") id . map (prt 0) . _unOrder

newtype Comma a = Comma { _unComma :: [a] }
  deriving (Eq, Ord, Read, Show)

instance Print a => Print (Comma a) where
  prt _i = prtSeq id id id (txt ",") id . map (prt 0) . _unComma

prettyError :: (a -> [String]) -> Err a -> [String]
prettyError prettyA = \case
  Bad e -> "  Error: " : map ("  "++) (lines e)
  Ok x  -> prettyA x

instance Print a => Print (Err a) where
  prt _ (Bad err) = txt ("Error: " ++ err)
  prt i (Ok  res) = prt i res

instance Print a => Print (Scoped a) where
  prt _i (Scoped ld x) =
    concatD [ doc (showString "let ") , prt 0 ld
            , doc (showString "in")
            , prt 0 x ]

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

instance Print N.Session where
  prt     i = prt i . reifySession
  prtList i = prtList i . reifySessions

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
