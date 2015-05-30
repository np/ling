module Lin.Session where

import Prelude hiding (log)
import Data.Maybe
import Lin.Norm

array :: TraverseKind -> Sessions -> Session
array ParK = Par
array TenK = Ten
array SeqK = Seq

one :: Session -> RSession
one s = Repl s (Lit 1)

list :: [Session] -> Sessions
list = map one

loli :: Session -> Session -> Session
loli s t = Par $ list [dual s, t]

fwd :: Int -> Session -> Session
fwd n s = Par . list $ s : dual s : replicate n (log s)

sort :: Typ -> Term -> Session
sort a e = Rcv (vec a e) (Snd (vec a e) End)

mapR :: (Session -> Session) -> RSession -> RSession
mapR f (Repl s a) = Repl (f s) a

mapSessions :: (Session -> Session) -> Sessions -> Sessions
mapSessions = map . mapR

class Dual a where
  dual :: a -> a

instance Dual RW where
  dual Read  = Write
  dual Write = Read

instance Dual Session where
  dual (Par s)    = Ten   (dual s)
  dual (Ten s)    = Par   (dual s)
  dual (Seq s)    = Seq   (dual s)
  dual (Snd a s)  = Rcv a (dual s)
  dual (Rcv a s)  = Snd a (dual s)
  dual (Atm p n)  = Atm (dual p) n
  dual End        = End

instance Dual RSession where
  dual = mapR dual

instance Dual a => Dual [a] where
  dual = map dual

log :: Session -> Session
log (Par s)    = Par (mapSessions log s)
log (Ten s)    = Par (mapSessions log s)
log (Seq s)    = Par (mapSessions log s)
log (Snd a s)  = Snd a (log s)
log (Rcv a s)  = Snd a (log s)
log (Atm _ n)  = Atm Write n
log End        = End

defaultEnd :: Maybe Session -> Session
defaultEnd Nothing  = End
defaultEnd (Just s) = s

sessionStep :: Session -> Session
sessionStep (Snd _ s) = s
sessionStep (Rcv _ s) = s
sessionStep s         = error $ "sessionStep: no steps " ++ show s

extractDuals :: Dual a => (Maybe a , Maybe a) -> Maybe (a , a)
extractDuals (Nothing , Nothing) = Nothing
extractDuals (Just s0 , Nothing) = Just (s0, dual s0)
extractDuals (Nothing , Just s1) = Just (dual s1, s1)
extractDuals (Just s0 , Just s1) = Just (s0, s1)

-- TODO: would it be nicer with the First monoid
extractSession :: [Maybe Session] -> Session
extractSession l =
  case catMaybes l of
    s:_ -> s
    _   -> error "Missing type signature in `new`"

flatRSession :: RSession -> [Session]
flatRSession (Repl s (Lit n)) = replicate (fromInteger n) s
flatRSession _ = error "flatRSession"

flatSessions :: Sessions -> [Session]
flatSessions = concatMap flatRSession

projRSessions :: Integer -> Sessions -> Session
projRSessions _ []
  = error "projRSessions: out of bound"
projRSessions n (Repl s a:ss)
  = case a of
      Lit i
        | n < i     -> s
        | otherwise -> projRSessions (n-i) ss
      _ -> error "projRSessions/Repl: only integer literals are supported"

projSession :: Integer -> Session -> Session
projSession n (Par ss) = projRSessions n ss
projSession n (Ten ss) = projRSessions n ss
projSession n (Seq ss) = projRSessions n ss
projSession _ _        = error "projSession: not a par/tensor/seq session"

replRSession :: (Session -> [RSession]) -> RSession -> RSession
replRSession r (Repl s (Lit 1)) = one $ replSession r s
replRSession _ _ = error "replRSession: undefined"

replRSessionTerm :: Term -> RSession -> RSession
replRSessionTerm t = replRSession (\s -> [Repl s t])

replRSessionInt :: Int -> RSession -> RSession
replRSessionInt n = replRSession (list . replicate n)

replSession :: (Session -> [RSession]) -> Session -> Session
replSession r (Ten [Repl s (Lit 1)]) = Ten $ r s
replSession r (Par [Repl s (Lit 1)]) = Par $ r s
replSession r (Seq [Repl s (Lit 1)]) = Seq $ r s
replSession _ _ = error "replSession: undefined"

replSessionTerm :: Term -> Session -> Session
replSessionTerm t = replSession (\s -> [Repl s t])

replSessionInt :: Int -> Session -> Session
replSessionInt n = replSession (list . replicate n)

-- -}
