{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}
module Ling.Session where

import Prelude hiding (log)
import Ling.Prelude
import Ling.Norm
import qualified Ling.Raw as Raw

array :: TraverseKind -> Sessions -> Session
array = Array

oneS :: Session -> RSession
oneS s = Repl s ø

list :: [Session] -> Sessions
list = map oneS

loli :: Session -> Session -> Session
loli s t = Array ParK $ list [dual s, t]

fwds :: Int -> Session -> Sessions
fwds n s
  | n <  0    = error "fwd: Negative number of channels to forward"
  | n == 0    = []
  | n == 1    = [oneS s]
  | otherwise = list $ s : dual s : replicate (n - 2) (log s)

fwd :: Int -> Session -> Session
fwd n s = Array ParK $ fwds n s

endS :: Session
endS = Array SeqK []

-- Here one can tune what we consider ended.
-- Being ended implies:
-- * No need to actually use the channel
-- * Forwarders thus never use them
-- For instance these could be ended.
-- * `Array _ []` (thus `{}` and `[]`)
-- * `Array _ [ended ,..., ended]`
isEnd :: Session -> Bool
isEnd = (==) endS

isEndR :: RSession -> Bool
isEndR (s `Repl` r) = isEnd s && Just 1 == isLitR r

unRepl :: RSession -> Session
unRepl (s `Repl` (isLitR -> Just 1)) = s
unRepl _                             = error "unRepl: unexpected replicated session"

wrapSessions :: [RSession] -> Session
wrapSessions [s `Repl` (isLitR -> Just 1)] = s
wrapSessions ss                            = Array ParK ss

mapR :: (Session -> Session) -> RSession -> RSession
mapR f (Repl s a) = Repl (f s) a

mapSessions :: (Session -> Session) -> Sessions -> Sessions
mapSessions = map . mapR

class Dual a where
  dual :: a -> a
  dual = dualOp DualOp

  log  :: a -> a
  log = dualOp LogOp

  sink :: Dual a => a -> a
  sink = dual . log

  dualOp :: Dual a => DualOp -> a -> a
  dualOp NoOp   = id
  dualOp DualOp = dual
  dualOp LogOp  = log
  dualOp SinkOp = sink

termS :: DualOp -> Term -> Session
termS o (TSession s) = dualOp o s
termS o           t  = TermS  o t

-- Sub-optimal but concise
isLog, isSink :: (Eq session, Dual session) => session -> Bool

isLog  s = s ==  log s
isSink s = s == sink s

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

instance Dual DualOp where
  dual DualOp = NoOp
  dual NoOp   = DualOp
  dual LogOp  = SinkOp
  dual SinkOp = LogOp
  log  _      = LogOp

instance Dual TraverseKind where
  dual ParK = TenK
  dual TenK = ParK
  dual SeqK = SeqK
  log  SeqK = SeqK
  log  _    = ParK

instance Dual Session where
  dualOp f = \case
    Array k s -> Array (dualOp f k) (dualOp f s)
    IO p a s  -> IO (dualOp f p) a (dualOp f s)
    TermS p t -> TermS (dualOp f p) t

instance Dual Raw.Term where
  dual (Raw.Dual s) =          s
  dual           s  = Raw.Dual s

  log s
    | Raw.RawApp (Raw.Var (Raw.Name "Log")) [_] <- s
      = s
    | otherwise
      = Raw.RawApp (Raw.Var (Raw.Name "Log")) [Raw.paren s]

instance Dual RSession where
  dual   = mapR dual
  log    = mapR log
  dualOp = mapR . dualOp

instance Dual a => Dual [a] where
  dual   = map dual
  log    = map log
  dualOp = map . dualOp

instance Dual Term where
  dualOp o = tSession . termS o

defaultEnd :: Maybe Session -> Session
defaultEnd Nothing  = endS
defaultEnd (Just s) = s

defaultEndR :: Maybe RSession -> RSession
defaultEndR Nothing  = oneS endS
defaultEndR (Just s) = s

sessionStep :: Session -> Session
sessionStep (IO _ _ s) = s
sessionStep s          = error $ "sessionStep: no steps " ++ show s

extractDuals :: Dual a => (Maybe a , Maybe a) -> Maybe (a , a)
extractDuals (Nothing , Nothing) = Nothing
extractDuals (Just s0 , Nothing) = Just (s0, dual s0)
extractDuals (Nothing , Just s1) = Just (dual s1, s1)
extractDuals (Just s0 , Just s1) = Just (s0, s1)

-- TODO: would it be nicer with the First monoid
extractSession :: [Maybe a] -> a
extractSession l =
  case catMaybes l of
    s:_ -> s
    _   -> error "Missing type signature in `new`"

flatRSession :: RSession -> [Session]
flatRSession (Repl s r)
  | Just n <- isLitR r = replicate (fromInteger n) s
  | otherwise          = error "flatRSession"

flatSessions :: Sessions -> [Session]
flatSessions = concatMap flatRSession

projRSessions :: Integer -> Sessions -> Session
projRSessions _ []
  = error "projRSessions: out of bound"
projRSessions n (Repl s r:ss)
  | Just i <- isLitR r = if n < i
                           then s
                           else projRSessions (n-i) ss
  | otherwise = error "projRSessions/Repl: only integer literals are supported"

projSession :: Integer -> Session -> Session
projSession n (Array _ ss) = projRSessions n ss
projSession _ _            = error "projSession: not an array (par,tensor,seq) session"

replRSession :: RFactor -> RSession -> RSession
replRSession r (Repl s t) = Repl s (r <> t)

-- -}
