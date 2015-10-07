module Ling.Check.Program where

import           Ling.Check.Base
import           Ling.Check.Core
import           Ling.Norm
import           Ling.Print
import           Ling.Utils

import           Control.Lens
import           Control.Monad.Reader
import           Data.Map             (union)

checkProgram :: Program -> TC ()
checkProgram (Program decs) = checkDecs decs

checkDecs :: [Dec] -> TC ()
checkDecs = foldr checkDec (return ())

checkDec :: Dec -> TC () -> TC ()
checkDec (Sig d typ mt)   kont = checkVarDef d typ mt kont
checkDec (Dat d cs)       kont = do
  checkNoDups ("in the definition of " ++ pretty d) cs
  checkNotIn evars "name" d
  mapM_ (checkNotIn ctyps "data constructor") cs
  local ((ctyps %~ union (l2m [ (c,d) | c <- cs ]))
        .(evars . at d .~ Just TTyp)
        .(ddefs . at d .~ Just cs)) kont
checkDec (Equal t1 t2 ty) kont = do
  checkTyp ty
  checkTerm ty t1
  checkTerm ty t2
  -- This should probably be a better check
  when (t1 /= t2) $
    tcError ("The term " ++ pretty t1
            ++ " is not equal to " ++ pretty t2)
  kont
