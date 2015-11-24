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

instance SubTerms Session where
  subTerms f = \case
    TermS p t  -> termS p <$> f t
    Array k ss -> Array k <$> subTerms f ss
    IO rw vd s -> IO rw <$> varDecTerms f vd <*> subTerms f s

instance SubTerms RSession where
  subTerms f (s `Repl` RFactor r) = Repl <$> subTerms f s <*> (RFactor <$> f r)

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
