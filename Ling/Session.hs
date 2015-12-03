{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

module Ling.Session where

import           Ling.Norm
import           Ling.Prelude
import qualified Ling.Raw     as Raw
import           Prelude      hiding (log)

array :: TraverseKind -> Sessions -> Session
array = Array

oneS :: Session -> RSession
oneS s = Repl s ø

loli :: Op2 Session
loli s t = Array ParK $ oneS <$> [dual s, t]

fwds :: Int -> Session -> Sessions
fwds n s
  | n <  0    = error "fwd: Negative number of channels to forward"
  | n == 0    = []
  | n == 1    = [oneS s]
  | otherwise = oneS <$> s : dual s : replicate (n - 2) (log s)

fwd :: Int -> Endom Session
fwd n s = Array ParK $ fwds n s

-- Here one can tune what we consider ended.
-- Being ended implies:
-- * No need to actually use the channel
-- * Forwarders thus never use them
-- For instance these could be ended.
-- * `Array _ []` (thus `{}` and `[]`)
-- * `Array _ [ended ,..., ended]`
endS :: Prism' Session ()
endS = only (Array SeqK [])

endRS :: Prism' RSession ()
endRS = nearly (oneS (endS # ())) $ \(s `Repl` r) -> endS `is` s && litR1 `is` r

endedS :: Iso' (Maybe Session) Session
endedS = non' endS

endedRS :: Iso' (Maybe RSession) RSession
endedRS = non' endRS

unRepl :: RSession -> Session
unRepl (s `Repl` r)
  | litR1 `is` r = s
  | otherwise    = error "unRepl: unexpected replicated session"

wrapSessions :: [RSession] -> Session
wrapSessions [s `Repl` (is litR1 -> True)] = s
wrapSessions ss                            = Array ParK ss

-- LENS ME
mapR :: Endom Session -> Endom RSession
mapR f (Repl s a) = Repl (f s) a

-- LENS ME
mapSessions :: Endom Session -> Endom Sessions
mapSessions = map . mapR

class Dual a where
  dual :: Endom a
  dual = dualOp DualOp

  log :: Endom a
  log = dualOp LogOp

  sink :: Dual a => Endom a
  sink = dual . log

  dualOp :: Dual a => DualOp -> Endom a
  dualOp NoOp   = id
  dualOp DualOp = dual
  dualOp LogOp  = log
  dualOp SinkOp = sink

  -- Laws:
  --   isLog . log  == const True
  --   isLog . dual == isSink
  isLog, isSink :: a -> Bool

  isSink = isLog . dual

dualized :: (Dual a, Dual b) => Iso a b a b
dualized = iso dual dual

termS :: DualOp -> Term -> Session
termS o (TSession s) = dualOp o s
termS o           t  = TermS  o t

validAx :: (Eq session, Dual session) => session -> [channel] -> Bool
-- Forwarding anything between no channels is always possible
validAx _ []          = True
-- At least two for the general case
validAx _ (_ : _ : _) = True
-- One is enough if the session is a Sink. A sink can be derived
-- alone. Another way to think of it is that in the case of a sink,
-- the other side is a Log and there can be any number of Logs.
validAx s (_ : _)     = isSink s

instance Dual RW where
  dual Read  = Write
  dual Write = Read
  log _      = Write
  isLog      = (== Write)

instance Dual DualOp where
  dual DualOp = NoOp
  dual NoOp   = DualOp
  dual LogOp  = SinkOp
  dual SinkOp = LogOp
  log  _      = LogOp
  isLog      = (== LogOp)

instance Dual TraverseKind where
  dual ParK = TenK
  dual TenK = ParK
  dual SeqK = SeqK
  log  SeqK = SeqK
  log  _    = ParK

  isLog  k = k == log  k
  isSink k = k == sink k
  -- TODO: can we relax those to:
  -- isLog  _  = True
  -- isSink _  = True

instance Dual Session where
  dualOp f = \case
    Array k s -> Array (dualOp f k) (dualOp f s)
    IO p a s  -> IO (dualOp f p) a (dualOp f s)
    TermS p t -> TermS (dualOp f p) t

  isLog = \case
    Array k s -> isLog (k, s)
    IO p _ s  -> isLog (p, s)
    TermS p _ -> isLog p

instance Dual Raw.Term where
  dual (Raw.Dual s) =          s
  dual           s  = Raw.Dual s

  log s
    | Raw.RawApp (Raw.Var (Raw.Name "Log")) [_] <- s =
        s
    | otherwise =
        Raw.RawApp (Raw.Var (Raw.Name "Log")) [Raw.paren s]

  isLog = error "Raw.Term.isLog: not implemented"

instance Dual RSession where
  dual   = mapR dual
  log    = mapR log
  dualOp = mapR . dualOp
  isLog  = isLog  . view rsession
  isSink = isSink . view rsession

instance (Dual a, Dual b) => Dual (a, b) where
  dual          = bimap dual dual
  log           = bimap log  log
  dualOp f      = bimap (dualOp f) (dualOp f)
  isLog  (x, y) = isLog  x && isLog  y
  isSink (x, y) = isSink x && isSink y

instance Dual a => Dual [a] where
  dual   = map dual
  log    = map log
  dualOp = map . dualOp
  isLog  = all isLog
  isSink = all isSink

instance Dual Term where
  dualOp o = view tSession . termS o
  isLog    = isLog . view (from tSession)

sessionStep :: Endom Session
sessionStep (IO _ _ s) = s
sessionStep s          = error $ "sessionStep: no steps " ++ show s

extractDuals :: Dual a => (Maybe a, Maybe a) -> Maybe (a, a)
extractDuals (Nothing, Nothing) = Nothing
extractDuals (Just s0, Nothing) = Just (s0, dual s0)
extractDuals (Nothing, Just s1) = Just (dual s1, s1)
extractDuals (Just s0, Just s1) = Just (s0, s1)

-- TODO: would it be nicer with the First monoid
extractSession :: [Maybe a] -> a
extractSession l = l ^? each . _Just ?| error "Missing type signature in `new`"

-- See flatRSession in Ling.Reduce
unsafeFlatRSession :: RSession -> [Session]
unsafeFlatRSession (s `Repl` r) =
  replicate (r ^? litR . integral ?| error "unsafeFlatRSession") s

-- See flatSessions in Ling.Reduce
unsafeFlatSessions :: Sessions -> [Session]
unsafeFlatSessions = concatMap unsafeFlatRSession

projRSessions :: Integer -> Sessions -> Session
projRSessions _ [] = error "projRSessions: out of bound"
projRSessions n (Repl s r:ss)
  | Just i <- r ^? litR = if n < i
                           then s
                           else projRSessions (n - i) ss
  | otherwise           = error "projRSessions/Repl: only integer literals are supported"

projSession :: Integer -> Endom Session
projSession n (Array _ ss) = projRSessions n ss
projSession _ _            = error "projSession: not an array (par,tensor,seq) session"

replRSession :: RFactor -> Endom RSession
replRSession r (Repl s t) = Repl s (r <> t)

-- -}
