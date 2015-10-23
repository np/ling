{-# LANGUAGE LambdaCase #-}
module Ling.Raw
  ( module Ling.Abs
  , module Ling.Raw
  )
  where

import           Ling.Abs

aTerm :: ATerm -> Term
aTerm (Paren t) = t
aTerm t         = RawApp t []

paren :: Term -> ATerm
paren (RawApp t []) = t
paren t             = Paren t

mkProcs :: [Proc] -> Proc
mkProcs = \case
  []  -> PPrll []
  [p] -> p
  ps  -> PPrll ps

pNxt :: Proc -> Proc -> Proc
pNxt proc0 (PPrll []) = proc0
pNxt proc0 proc1      = proc0 `PNxt` proc1

pDot :: Proc -> Proc -> Proc
pDot proc0 (PPrll []) = proc0
pDot proc0 proc1      = proc0 `PDot` proc1
