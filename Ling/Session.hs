{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

module Ling.Session
  (module Ling.Session
  ,module Ling.Session.Core) where

import Ling.Session.Core
import           Ling.Defs
import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Scoped
import           Prelude      hiding (log)

unRepl :: RSession -> Session
unRepl (s `Repl` r)
  | litR1 `is` r = s
  | otherwise    = error "unRepl: unexpected replicated session"

wrapSessions :: Sessions -> Session
wrapSessions (Sessions [s `Repl` (is litR1 -> True)]) = s
wrapSessions ss                                       = Array ParK ss

constArrOp :: TraverseKind -> SessionOp
constArrOp = SessionOp idEndom . constEndom

constRWOp :: RW -> SessionOp
constRWOp rw = SessionOp (constEndom rw) idEndom

sessionStep :: Term -> Endom Session
sessionStep tm (IO _ (Arg x mty) s) = mkLet__ $ subst1 (x, Ann mty tm) s
sessionStep _  s                    = error $ "sessionStep: no steps " ++ show s

-- Should be length preserving
extractDuals :: Dual a => [Maybe a] -> [a]
extractDuals = \case
  [Just s0, Nothing] -> [s0, dual s0]
  [Nothing, Just s1] -> [dual s1, s1]

  -- Appart from the two cases above the general rule
  -- so far is that all sessions should be annotated
  mas -> mas ^? below _Just ?| error "Missing type signature in `new` (extractDuals)"

extractSession :: [Maybe a] -> a
extractSession l = l ^? each . _Just ?| error "Missing type signature in `new` (extractSession)"

-- See flatRSession in Ling.Reduce
unsafeFlatRSession :: RSession -> [Session]
unsafeFlatRSession (s `Repl` r) =
  replicate (r ^? litR . integral ?| error ("unsafeFlatRSession " ++ show r)) s

-- See flatSessions in Ling.Reduce
unsafeFlatSessions :: Sessions -> [Session]
unsafeFlatSessions = concatMap unsafeFlatRSession . view _Sessions

projSessions :: Integer -> Sessions -> Session
projSessions _ (Sessions []) = error "projSessions: out of bound"
projSessions n (Sessions (Repl s r:ss))
  | Just i <- r ^? litR = if n < i
                           then s
                           else projSessions (n - i) (Sessions ss)
  | otherwise           = error "projSessions/Repl: only integer literals are supported"

replRSession :: RFactor -> Endom RSession
replRSession r (Repl s t) = Repl s (r <> t)

mkCaseRSession :: (Scoped Term -> Term) -> Rel (Scoped Term) -> MkCase' (Scoped RSession)
mkCaseRSession f rel u = repl . bimap h h . unzip . fmap unrepl
  where
    repl   (s, r)    = pure $ (s ^. from tSession) `Repl` (r ^. from rterm)
    unrepl (con, rs) = ((con, view (rsession . tSession) <$> rs),
                        (con, view (rfactor  . rterm)    <$> rs))
    h                = mkCaseBy f rel u

mkCaseSessions :: (Scoped Term -> Term) -> Rel (Scoped Term) -> MkCase' (Scoped Sessions)
mkCaseSessions f rel u brs =
  Sessions . pure <$> mkCaseRSession f rel u (brs & branches . scoped %~ unSingleton)
  where
    unSingleton (Sessions [x]) = x
    unSingleton _              = error "mkCaseSessions"
-- -}
