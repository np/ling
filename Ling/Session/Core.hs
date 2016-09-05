{-# LANGUAGE LambdaCase   #-}

module Ling.Session.Core
  ( array
  , loli
  , oneS
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

array :: TraverseKind -> [RSession] -> Session
array k = Array k . Sessions

oneS :: Session -> RSession
oneS s = Repl s ø

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
endRS = nearly (oneS (endS # ())) $ \(s `Repl` r) -> endS `is` s && litR1 `is` r

endedS :: Iso' (Maybe Session) Session
endedS = non' endS

endedRS :: Iso' (Maybe RSession) RSession
endedRS = non' endRS

logOp :: SessionOp
logOp = SessionOp (constEndom Write) (ifEndom TenK ParK (ifEndom ParK ParK (constEndom SeqK)))

dualOp :: SessionOp
dualOp = SessionOp (ifEndom Read Write (constEndom Read))
                   (ifEndom TenK ParK  (ifEndom ParK TenK (constEndom SeqK)))

-- Laws (not the minimal set):
-- * dual . dual = id
-- * log . log = log
-- * the sessionOp default definition should hold
class Dual a where
  dual :: Endom a
  dual = sessionOp dualOp

  log :: Endom a
  log = sessionOp logOp

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
  sessionOp (SessionOp rwf kf) (SessionOp rwg kg) =
    SessionOp (composeFinEndom rwf rwg) (composeFinEndom kf kg)
  isMaster  (SessionOp rwf kf) = isMaster (rwf, kf)

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

  log s
    | Raw.RawApp (Raw.Var (Raw.Name "Log")) [_] <- s =
        s
    | otherwise =
        Raw.RawApp (Raw.Var (Raw.Name "Log")) [Raw.paren s]

  sessionOp f
    | f == idOp        = id
    | f == dualOp      = dual
    | f == logOp       = log
    | f == dual logOp  = dual . log
    | otherwise        = error $ "Raw.Term.sessionOp: not implemented " ++ show f

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
