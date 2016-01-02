{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.SubTerms where

import Ling.Norm
import Ling.Prelude
import Ling.Session

class SubTerms a where
  subTerms :: Traversal' a Term

instance SubTerms a => SubTerms (Maybe a) where
  subTerms = _Just . subTerms

instance SubTerms a => SubTerms [a] where
  subTerms = list . subTerms

instance (SubTerms a, SubTerms b) => SubTerms (a, b) where
  subTerms = subTerms `beside` subTerms

instance SubTerms NewPatt where
  subTerms f = \case
    NewChans k cds -> NewChans k <$> subTerms f cds
    NewChan  c os  -> NewChan c <$> _Just f os

instance SubTerms Session where
  subTerms f = \case
    TermS p t  -> termS p <$> f t
    Array k ss -> Array k <$> subTerms f ss
    IO rw vd s -> IO rw <$> varDecTerms f vd <*> subTerms f s

instance SubTerms RFactor where
  subTerms = _RFactor

instance SubTerms RSession where
  subTerms f (s `Repl` r) = Repl <$> subTerms f s <*> subTerms f r

instance SubTerms ChanDec where
  subTerms f (ChanDec c r os) = ChanDec c <$> subTerms f r <*> subTerms f os

instance SubTerms a => SubTerms (Arg a) where
  subTerms = argTerms subTerms

argTerms :: Traversal' a Term -> Traversal' (Arg a) Term
argTerms trv f (Arg x b) = Arg x <$> trv f b

varDecTerms :: Traversal' VarDec Term
varDecTerms = argTerms _Just

absTerms :: Traversal' (VarDec, Term) Term
absTerms = varDecTerms `beside` id

instance SubTerms CPatt where
  subTerms f = \case
    ChanP cd      -> ChanP <$> subTerms f cd
    ArrayP k pats -> ArrayP k <$> subTerms f pats
