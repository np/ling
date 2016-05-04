{-# LANGUAGE GeneralizedNewtypeDeriving   #-}
{-# LANGUAGE LambdaCase                   #-}
{-# LANGUAGE Rank2Types                   #-}
{-# LANGUAGE TemplateHaskell              #-}
module Ling.Reduce where

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Print
import           Ling.Scoped
import           Ling.Session

newtype Reduced a = Reduced { _reduced :: Scoped a }
  deriving (Eq, Monoid)

makePrisms ''Reduced
makeLenses ''Reduced

instance Print a => Print (Reduced a) where
  prt i = prt i . view reduced

type Reduce a = Scoped a -> Reduced a

reduceApp :: Scoped Term -> [Term] -> Reduced Term
reduceApp st0 = \case
  []     -> rt1
  (u:us) ->
    case st1 ^. scoped of
      Lam (Arg x mty) t2 -> reduceApp (st1 *> subst1 (x, Ann mty u) t2) us
      Def x es           -> Reduced $ st1 $> Def x (es ++ u : us)
      _                  -> error "Ling.Reduce.reduceApp: IMPOSSIBLE"

  where
    rt1 = reduceTerm st0
    st1 = rt1 ^. reduced

reduceCase :: Scoped Term -> [Branch] -> Reduced Term
reduceCase st0 brs =
  case st1 ^. reduced . scoped of
    Con{} -> reduceTerm (st0 *> scase)
    _     -> Reduced scase

  where st1   = reduceTerm st0
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

reduceDef :: Scoped Name -> [Term] -> Reduced Term
reduceDef sd es
  | Just st <- scopedName sd              = reduceApp st es
  | Just ls <- es ^? below _Lit
  , Just  l <- reducePrim (unName # d) ls = Reduced . pure $ Lit l
  | "_:_" <- unName # d, [_,e] <- es      = Reduced . pure $ e
  | otherwise                             = Reduced $ sd $> Def d es

  where d = sd ^. scoped

reduceTerm :: Reduce Term
reduceTerm st0 =
  case t0 of
    Let defs t  -> reduceTerm (st0 *> Scoped ø defs () $> t)
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
    TSession s0 ->
      case s0 of
        TermS p t1 -> reduceTerm (st0 $> t1) & reduced . scoped %~ sessionOp p
        Array k ss -> Reduced $ st0 $> Array k ss ^. tSession
        IO rw vd s -> Reduced $ st0 $> IO rw vd s ^. tSession

  where t0 = st0 ^. scoped

reduce_ :: Traversal' s Term -> Reduce s
reduce_ trv s = Reduced $ trv (view reduced . reduceTerm . (s $>)) (s ^. scoped)

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

flatSessions :: Reduce Sessions
flatSessions ss = Reduced . sequenceA $ (ss ^. scoped) >>= flatRSession . (ss $>)
