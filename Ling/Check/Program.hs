module Ling.Check.Program where

import           Ling.Check.Base
import           Ling.Check.Core
import           Ling.Norm
import           Ling.Print
import           Ling.Prelude

import           Data.Map        (union)

checkProgram :: Program -> TC ()
checkProgram (Program decs) = checkDecs decs

checkDecs :: [Dec] -> TC ()
checkDecs = foldr checkDec (return ())

checkDec :: Dec -> Endom (TC a)
checkDec (Sig d typ mt)   kont = checkVarDef d typ mt kont
checkDec (Dat d cs)       kont = do
  errorScope d $ do
    checkNoDups ("in the definition of " ++ pretty d) cs
    checkNotIn evars "name" d
    for_ cs (checkNotIn ctyps "data constructor")
  local ((ctyps %~ union (l2m [ (c,d) | c <- cs ]))
        .(evars . at d ?~ TTyp)
        .(ddefs . at d ?~ cs)) kont
checkDec (Assert a) kont = checkAsr a kont

checkAsr :: Assertion -> Endom (TC a)
checkAsr (Equal t1 t2 ty) kont = do
  checkTyp ty
  checkTerm ty t1
  checkTerm ty t2

  checkEquivalence "Terms are not equivalent."
    "Left side:"  (pure t1)
    "Right side:" (pure t2)

  kont
