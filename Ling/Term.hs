module Ling.Term where

import Ling.Abs
import qualified Ling.Norm as N

eAdd :: Term -> Term -> Term
eAdd e0 e1 = Infix e0 Plus e1

nAdd :: N.Term -> N.Term -> N.Term
nAdd e0 e1 = N.Def (Name "_+_") [e0, e1]
