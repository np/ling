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

-- It would be dangerous to make Reduced a Functor/Applicative
-- since this would work only for reduced-form-preserving functions.
-- At the same time lenses provide with a workaround, so what's
-- worse?
newtype Reduced a = Reduced { _reduced :: Scoped a }
  deriving (Eq, Show, Monoid)

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
      Lam (Arg x mty) t2 -> reduceApp (st1 *> subst1 (x, Ann mty u) t2) us
      Def x es           -> Reduced $ st1 $> Def x (es ++ u : us)
      _                  -> error "Ling.Reduce.reduceApp: IMPOSSIBLE"

  where
    rt1 = reduce st0
    st1 = rt1 ^. reduced

reduceCase :: Scoped Term -> [Branch] -> Reduced Term
reduceCase st0 brs =
  case st1 ^. scoped of
    Con{} -> reduce (st0 *> scase)
    _     -> Reduced scase

  where st1   = reduce st0 ^. reduced
        scase = (`mkCase` brs) <$> st1

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

reduceDef :: Scoped Name -> [Term] -> Reduced Term
reduceDef sd es
  | Just st <- scopedName sd              = reduceApp st es
  | Just ls <- es ^? below _Lit
  , Just  l <- reducePrim (unName # d) ls = Reduced . pure $ Lit l
  | "_:_" <- unName # d, [_,e] <- es      = Reduced . pure $ e
  | otherwise                             = Reduced $ sd $> Def d es

  where d = sd ^. scoped

instance HasReduce a b => HasReduce (Maybe a) (Maybe b) where
  reduce sma =
    case sma ^. scoped of
      Just a  -> reduce (sma $> a) & reduced . scoped %~ Just
      Nothing -> Reduced $ pure Nothing

instance HasReduce Session Session where
  reduce s0 =
    case s0 ^. scoped of
      TermS p t1 -> reduce (s0 $> t1) & reduced . scoped %~ (view (from tSession) . sessionOp p)
      Array k ss -> Reduced $ s0 $> Array k ss
      IO rw vd s -> Reduced $ s0 $> IO rw vd s

instance HasReduce RFactor RFactor where
  reduce = reduce_ rterm

instance HasReduce RSession RSession where
  reduce rs0 =
    case rs0 ^. scoped of
      s `Repl` r -> Reduced (Repl <$> reduce (rs0 $> s) ^. reduced <*> reduce (rs0 $> r) ^. reduced)

instance HasReduce ChanDec ChanDec where
  reduce scd =
    case scd ^. scoped of
      ChanDec c r os -> Reduced
        (ChanDec c
          <$> (reduce (scd $> r) ^. reduced)
          <*> (reduce (scd $> os) ^. reduced))

instance HasReduce Term Term where
  reduce st0 =
    case t0 of
      Let defs t  -> reduce (st0 *> Scoped ø defs () $> t)
      Def d es    -> reduceDef  (st0 $> d) es
      Case t brs  -> reduceCase (st0 $> t) brs
      Lit{}       -> Reduced $ pure t0
      TTyp        -> Reduced $ pure t0
      Con{}       -> Reduced $ pure t0
      Lam{}       -> Reduced st0
      Proc{}      -> Reduced st0
      TFun{}      -> Reduced st0
      TSig{}      -> Reduced st0
      TProto{}    -> Reduced st0
      TSession s0 -> reduce (st0 $> s0) & reduced . scoped %~ view tSession

    where t0 = st0 ^. scoped

-- TODO assumptions!!!
reduce_ :: HasReduce' a => Traversal' s a -> Reduce' s
reduce_ trv s = Reduced $ trv (view reduced . reduce . (s $>)) (s ^. scoped)

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

instance HasReduce Sessions Sessions where
  reduce ss = Reduced . fmap Sessions . sequenceA $ (ss ^. scoped . _Sessions) >>= flatRSession . (ss $>)

-- This is not really about some sort of Weak Head Normal Form.
-- What matters is to reduce the At constructor:
--   @(proc(Γ) P){Γ} -> P
instance HasReduce Proc Proc where
  reduce sp =
    case sp ^. scoped of
      Act act -> reduce_ (_ActAt . _1) (sp $> Act act)
      proc0 `Dot` proc1 ->
        Reduced (dotP <$> sproc0 <*> sproc1)
        where
          sproc0, sproc1 :: Scoped Proc
          sproc0 = reduce (sp $> proc0) ^. reduced
          sproc1 = reduce (sp $> proc1) ^. reduced
      NewSlice{} -> Reduced sp
      Procs procs -> Reduced $ procs ^. each . to (view reduced . reduce . (sp $>))
