{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

module Ling.Session.Core
  ( wrapSessions
  , tProto
  , array
  , loli
  , oneS
  , _OneS
  , unsafeUnRepl
  , fwds
  , fwd
  , endS
  , endRS
  , endedS
  , endedRS
  , logOp
  , dualOp
  , dualized
  , termS
  , Dual(..)
  ) where

import           Ling.Norm
import           Ling.Prelude
import qualified Ling.Raw     as Raw
import           Prelude      hiding (log)

-- oneS s = _OneS # s
oneS :: Session -> RSession
oneS s = Repl s ø

_OneS :: Prism' RSession Session
_OneS = prism oneS $ \case
  sr@(Repl s r)
    | r == ø    -> Right s
    | otherwise -> Left sr

unsafeUnRepl :: RSession -> Session
unsafeUnRepl sr = sr ^? _OneS ?| error "unsafeUnRepl: unexpected replicated session"

wrapSessions :: Sessions -> Session
wrapSessions (Sessions [sr]) | Just s <- sr ^? _OneS = s
wrapSessions ss                                      = Array ParK ss

tProto :: [RSession] -> Typ
tProto = TProto . Sessions . pure . oneS . wrapSessions . Sessions

array :: TraverseKind -> [RSession] -> Session
array k = Array k . Sessions

loli :: Op2 Session
loli s t = Array ParK . Sessions $ oneS <$> [dual s, t]

fwds :: Dual session => Int -> session -> [session]
fwds n s
  | n <  0    = error "fwd: Negative number of channels to forward"
  | n == 0    = []
  | n == 1    = [s]
  | otherwise = s : dual s : replicate (n - 2) (log s)

fwd :: Int -> Endom Session
fwd n s = Array ParK . Sessions $ oneS <$> fwds n s

-- Here one can tune what we consider ended.
-- Being ended implies:
-- * No need to actually use the channel
-- * Forwarders thus never use them
-- For instance these could be ended.
-- * `Array _ []` (thus `{}` and `[]`)
-- * `Array _ [ended ,..., ended]`
endS :: Prism' Session ()
endS = only (Array SeqK ø)

endRS :: Prism' RSession ()
endRS = nearly (oneS (endS # ())) $ \(s `Repl` r) -> (s & is endS) && (r & is litR1)

endedS :: Iso' (Maybe Session) Session
endedS = non' endS

endedRS :: Iso' (Maybe RSession) RSession
endedRS = non' endRS

logOp :: SessionOp
logOp = SessionOp (constEndom Write) (ifEndom TenK ParK (ifEndom ParK ParK (constEndom SeqK)))

-- I guess that dualOp raises SessionOp from a monoid to a group.
dualOp :: SessionOp
dualOp = SessionOp (ifEndom Read Write (constEndom Read))
                   (ifEndom TenK ParK  (ifEndom ParK TenK (constEndom SeqK)))

constArrOp :: TraverseKind -> SessionOp
constArrOp = SessionOp ø . constEndom

constRWOp :: RW -> SessionOp
constRWOp rw = SessionOp (constEndom rw) ø

seqOp :: SessionOp
seqOp = constArrOp SeqK

sendOp :: SessionOp
sendOp = constRWOp Write

recvOp :: SessionOp
recvOp = constRWOp Read

-- Laws (not the minimal set):
-- * dual . dual = id
-- * log . log = log
-- * the sessionOp default definition should hold
class Dual a where
  dual :: Endom a
  dual = sessionOp dualOp

  log :: Endom a
  log = sessionOp logOp

  seq_ :: Endom a
  seq_ = sessionOp seqOp

  send_ :: Endom a
  send_ = sessionOp sendOp

  recv_ :: Endom a
  recv_ = sessionOp sendOp

  sessionOp :: Dual a => SessionOp -> Endom a

  -- Being master only concerns the top part of the session. The rule being
  -- that only one when composing several sessions only one can be master.
  isMaster :: a -> Bool

dualized :: (Dual a, Dual b) => Iso a b a b
dualized = iso dual dual

termS :: SessionOp -> Term -> Session
termS o (TSession s) = sessionOp o s
termS o           t  = TermS  o t

instance Dual RW where
  dual Read  = Write
  dual Write = Read

  log        = const Write

  sessionOp (SessionOp rwf _) = evalFinEndom rwf

  isMaster   = (== Write)

instance (Ord a, Dual a) => Dual (FinEndom a) where
  sessionOp f = error $ "FinEndom.sessionOp: not implemented " ++ show f
  isMaster (FinEndom m d) = anyOf each isMaster m || isMaster d

instance Dual SessionOp where
  sessionOp = (<>)
  isMaster (SessionOp rwf kf) = isMaster (rwf, kf)

instance Dual TraverseKind where
  dual ParK = TenK
  dual TenK = ParK
  dual SeqK = SeqK

  log  SeqK = SeqK
  log  _    = ParK

  sessionOp (SessionOp _ kfun) = evalFinEndom kfun

  isMaster  = (== ParK)

instance Dual Session where
  sessionOp f = \case
    Array k s -> Array (sessionOp f k) (sessionOp f s)
    IO p a s  -> IO (sessionOp f p) a (sessionOp f s)
    TermS o t -> TermS (sessionOp f o) t

  isMaster = \case
    Array k _ -> isMaster k
    IO p _ _  -> isMaster p
    TermS o _ -> isMaster o

instance Dual Raw.Term where
  dual (Raw.Dual s) =          s
  dual           s  = Raw.Dual s

  log s0 = Raw.mkPrimOp "Log" [logBody] where
    logBody
      | Just (x,[s1]) <- s0 ^? Raw._PrimOp
      , x `elem` ["Log","Send","Recv"]     = s1
      | otherwise                          = s0

  seq_ s0
    | Just ("Log",[s1]) <- s0 ^? Raw._PrimOp = Raw.mkPrimOp "Seq" [Raw.mkPrimOp "Send" [s1]]
    | Just ("Seq",_)    <- s0 ^? Raw._PrimOp = s0
    | otherwise                              = Raw.mkPrimOp "Seq" [s0]

  send_ s0
    | Just ("Seq",[s1]) <- s0 ^? Raw._PrimOp = Raw.mkPrimOp "Seq" [Raw.mkPrimOp "Send" [s1]]
    | Just (x,_)        <- s0 ^? Raw._PrimOp
    , x `elem` ["Send", "Recv", "Log"]       = s0
    | otherwise                              = Raw.mkPrimOp "Send" [s0]

  recv_ s0
    | Just ("Seq",[s1]) <- s0 ^? Raw._PrimOp = Raw.mkPrimOp "Seq" [Raw.mkPrimOp "Recv" [s1]]
    | Just (x,_)        <- s0 ^? Raw._PrimOp
    , x `elem` ["Send", "Recv"]              = s0
    | otherwise                              = Raw.mkPrimOp "Recv" [s0]

  sessionOp f
    | Just g <- lookup f        ops = g
    | Just g <- lookup (dual f) ops = dual . g
    | otherwise                     = error $ "Raw.Term.sessionOp: not implemented " ++ show f

    where
      ops =
        [(ø, id)
        ,(logOp,  log)
        ,(seqOp,  seq_)
        ,(sendOp, send_)
        ,(recvOp, recv_)
        ,(seqOp <> sendOp,  seq_ . send_)
        ,(seqOp <> recvOp,  seq_ . recv_)
        ]

  isMaster  = error "Raw.Term.isMaster: not implemented"

instance Dual RSession where
  dual   = rsession %~ dual
  log    = rsession %~ log
  sessionOp = over rsession . sessionOp
  isMaster = isMaster . view rsession

instance (Dual a, Dual b) => Dual (a, b) where
  dual     = bimap dual dual
  log      = bimap log  log
  sessionOp f = bimap (sessionOp f) (sessionOp f)
  isMaster (a,b) = isMaster a || isMaster b

instance Dual a => Dual [a] where
  dual   = map dual
  log    = map log
  sessionOp = map . sessionOp
  isMaster = any isMaster

instance Dual Sessions where
  dual   = _Sessions %~ dual
  log    = _Sessions %~ log
  sessionOp = over _Sessions . sessionOp
  isMaster = isMaster . view _Sessions

instance Dual Term where
  sessionOp o = view tSession . termS o
  isMaster = isMaster . view (from tSession)
-- -}
