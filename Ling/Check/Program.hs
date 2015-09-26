module Ling.Check.Program where

import           Ling.Check.Base
import           Ling.Check.Core
import           Ling.Norm
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
