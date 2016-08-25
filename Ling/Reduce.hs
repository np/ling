{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving   #-}
{-# LANGUAGE LambdaCase                   #-}
{-# LANGUAGE MultiParamTypeClasses        #-}
{-# LANGUAGE Rank2Types                   #-}
{-# LANGUAGE TemplateHaskell              #-}
module Ling.Reduce where

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Print
import           Ling.Proc
import           Ling.Scoped
import           Ling.Session.Core

-- This `strong` mode is not really useful. Ling.Subst is already
-- implementing the strong reductfuse semantics so Ling.Reduce
-- can be kept as the lazy/weak version.
strong :: Bool
strong = False

newtype Reduced a = Reduced { _reduced :: Scoped a }
  deriving (Eq, Monoid, Functor, Applicative)

makePrisms ''Reduced
makeLenses ''Reduced

instance Print a => Print (Reduced a) where
  prt i = prt i . view reduced

type Reduce a b = Scoped a -> Reduced b
type Reduce' a = Reduce a a

class HasReduce a b where
  reduce :: Reduce a b

type HasReduce' a = HasReduce a a

reduceApp :: Scoped Term -> [Term] -> Reduced Term
reduceApp st0 = \case
  []     -> rt1
  (u:us) ->
    case st1 ^. scoped of
      Lam (Arg x mty) t2 -> reduceApp (st0 *> st1 *> subst1 (x, Ann mty u) t2) us
      Def k d es -> reduceDef (st0 *> st1 $> (k, d, es ++ u : us))
      _ -> error "Ling.Reduce.reduceApp: IMPOSSIBLE"

  where
    rt1 = reduce st0
    st1 = rt1 ^. reduced
    -- st1 might have less (or even no) defs than st0.

reduceCase :: Scoped Term -> [Branch] -> Reduced Term
reduceCase st0 brs =
  case st1 ^. reduced . scoped of
    Con{} -> reduce (st0 *> scase)
    _ | strong    -> Reduced scase
      | otherwise -> mkCase <$> st1 <*> reduce (st0 $> brs)

  where st1   = reduce st0
        scase = (`mkCase` brs) <$> st1 ^. reduced

reducePrim :: String -> [Literal] -> Maybe Literal
reducePrim "_+_"        [LInteger x, LInteger y] = Just $ LInteger (x + y)
reducePrim "_-_"        [LInteger x, LInteger y] = Just $ LInteger (x - y)
reducePrim "_*_"        [LInteger x, LInteger y] = Just $ LInteger (x * y)
reducePrim "_/_"        [LInteger x, LInteger y] = Just $ LInteger (x `div` y)
reducePrim "_%_"        [LInteger x, LInteger y] = Just $ LInteger (x `mod` y)
reducePrim "pow"        [LInteger x, LInteger y] = Just $ LInteger (x ^ y)
reducePrim "_+D_"       [LDouble  x, LDouble  y] = Just $ LDouble  (x + y)
reducePrim "_-D_"       [LDouble  x, LDouble  y] = Just $ LDouble  (x - y)
reducePrim "_*D_"       [LDouble  x, LDouble  y] = Just $ LDouble  (x * y)
reducePrim "_/D_"       [LDouble  x, LDouble  y] = Just $ LDouble  (x / y)
reducePrim "powD"       [LDouble  x, LDouble  y] = Just $ LDouble  (x ** y)
reducePrim "_++S_"      [LString  x, LString  y] = Just $ LString  (x ++ y)
reducePrim "Int2Double" [LInteger x]             = Just $ LDouble  (fromInteger x)
reducePrim "showInt"    [LInteger x]             = Just $ LString  (show x)
reducePrim "showDouble" [LDouble  x]             = Just $ LString  (show x)
reducePrim "showChar"   [LChar    x]             = Just $ LString  (show x)
reducePrim "showString" [LString  x]             = Just $ LString  (show x)
reducePrim _            _                        = Nothing

reduceDef :: Scoped (DefKind, Name, [Term]) -> Reduced Term
reduceDef sdef =
  -- traceReduce "reduceDef" sdef $
  case sdef ^. scoped of
    (k, d, es) ->
      case k of
        Defined
          | Just st <- scopedName (sdef $> d) -> reduceApp st es
        Undefined
          | Just ls <- es' ^? reduced . scoped . below _Lit
          , Just  l <- reducePrim (unName # d) ls -> pure $ Lit l
        _ -> Def k d <$> es'
      where
        es' = reduce (sdef $> es)

instance HasReduce a b => HasReduce (Maybe a) (Maybe b) where reduce = reduceEach
instance HasReduce a b => HasReduce [a] [b]             where reduce = reduceEach
instance HasReduce a b => HasReduce (Arg a) (Arg b)     where reduce = reduceEach

instance (HasReduce a b, HasReduce a' b') => HasReduce (a, a') (b, b') where
  reduce sxy = bitraverse (reduce . (sxy $>)) (reduce . (sxy $>)) (sxy ^. scoped)

-- Only needed for ConName
instance HasReduce Name Name where reduce = Reduced

instance HasReduce Session Session where
  reduce s0 =
    case s0 ^. scoped of
      TermS p t1 -> (view (from tSession) . sessionOp p) <$> reduce (s0 $> t1)
      Array k ss -> whenStrong $ Array k <$> reduce (s0 $> ss)
      IO rw vd s -> whenStrong $ IO rw <$> reduce (s0 $> vd) <*> reduce (s0 $> s)
    where
      whenStrong s | strong    = s
                   | otherwise = Reduced s0

instance HasReduce RFactor RFactor where
  reduce = reduce_ rterm

instance HasReduce RSession RSession where
  reduce rs0 =
    case rs0 ^. scoped of
      s `Repl` r -> Repl <$> reduce (rs0 $> s) <*> reduce (rs0 $> r)

instance HasReduce ChanDec ChanDec where
  reduce scd =
    case scd ^. scoped of
      ChanDec c r os -> ChanDec c <$> reduce (scd $> r) <*> reduce (scd $> os)

instance HasReduce Term Term where
  reduce st0 =
    case t0 of
      Let defs t  -> reduce (st0 *> Scoped ø defs () $> t)
      Def k d es  -> reduceDef (st0 $> (k, d, es))
      Case t brs  -> reduceCase (st0 $> t) brs
      Lit{}       -> pure t0
      TTyp        -> pure t0
      Con{}       -> pure t0
      Proc cds p  -> whenStrong $ Proc <$> reduce (st0 $> cds) <*> reduce (st0 $> p)
      Lam  arg t  -> whenStrong $ Lam <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TFun arg t  -> whenStrong $ TFun <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TSig arg t  -> whenStrong $ TSig <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TProto ss   -> whenStrong $ TProto <$> reduce (st0 $> ss)
      TSession s0 -> view tSession <$> reduce (st0 $> s0)

    where
      t0 = st0 ^. scoped
      whenStrong s | strong    = s
                   | otherwise = Reduced st0

-- TODO assumptions!!!
reduce_ :: HasReduce a b => Traversal s t a b -> Reduce s t
reduce_ trv ss = trv (reduce . (ss $>)) (ss ^. scoped)

reduceEach :: (Each s t a b, HasReduce a b) => Reduce s t
reduceEach = reduce_ each

flatRSession :: Scoped RSession -> [Scoped RSession]
flatRSession ssr
  | Just n <- r1 ^? litR . integral = replicate n (pure $ oneS s)
  | Just (rL,rR) <- r1 ^? addR      = flatRSession (sr1 $> s `Repl` rL)
                                   ++ flatRSession (sr1 $> s `Repl` rR)
  | otherwise                       = [ssr]

  where sr1 = reduce_ rterm (ssr $> r0) ^. reduced
        s   = ssr ^. scoped . rsession
        r0  = ssr ^. scoped . rfactor
        r1  = sr1 ^. scoped

flatRSessions :: Scoped Sessions -> [Scoped RSession]
flatRSessions sss = sss ^. scoped . _Sessions >>= flatRSession . (sss $>)

instance HasReduce Sessions Sessions where
  reduce = Reduced . fmap Sessions . sequenceA . flatRSessions

-- This is not really about some sort of Weak Head Normal Form.
-- What matters is to reduce the At constructor:
--   @(proc(Γ) P){Γ} -> P
instance HasReduce Proc Proc where
  reduce sp =
    case sp ^. scoped of
      Act act -> reduce_ (_ActAt . _1) (sp $> Act act)
      proc0 `Dot` proc1 -> (dotP :: Op2 Proc) <$> reduce (sp $> proc0) <*> reduce (sp $> proc1)
      NewSlice cs r n p
        | strong    -> NewSlice cs <$> reduce (sp $> r) <*> pure n <*> reduce (sp $> p)
        | otherwise -> Reduced sp
      Procs procs -> procs ^. each . to (reduce . (sp $>))
