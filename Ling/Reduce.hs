{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.Reduce where

import           Ling.Defs ()
import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Scoped
import           Ling.Session

reduceApp :: Scoped Term -> [Term] -> Scoped Term
reduceApp st0 = \case
  []     -> st1
  (u:us) ->
    case st1 ^. scoped of
      Lam (Arg x mty) t2 -> reduceApp (st1 *> subst1 (x, Ann mty u) t2) us
      Def x es           -> st1 $> Def x (es ++ u : us)
      _                  -> error "Ling.Reduce.reduceApp: IMPOSSIBLE"

  where st1 = reduceTerm st0

reduceCase :: Scoped Term -> [Branch] -> Scoped Term
reduceCase st0 brs =
  case st1 ^. scoped of
    Con{} -> reduceTerm scase
    _     -> scase

  where st1   = reduceTerm st0
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

reduceDef :: Scoped Name -> [Term] -> Scoped Term
reduceDef sd es
  | Just st <- scopedName sd              = reduceApp st es
  | Just ls <- es ^? below _Lit
  , Just  l <- reducePrim (unName # d) ls = pure $ Lit l
  | otherwise                             = sd $> Def d es

  where d = sd ^. scoped

reduceTerm :: Endom (Scoped Term)
reduceTerm st0 =
  case t0 of
    Let defs t  -> reduceTerm (st0 *> Scoped ø defs () $> t)
    Def d es    -> reduceDef  (st0 $> d) es
    Case t brs  -> reduceCase (st0 $> t) brs
    Lit{}       -> pure t0
    TTyp        -> pure t0
    Con{}       -> pure t0
    Lam{}       -> st0
    Proc{}      -> st0
    TFun{}      -> st0
    TSig{}      -> st0
    TProto{}    -> st0
    TSession s0 ->
      view tSession <$> case s0 of
        TermS p t1 -> termS p <$> reduceTerm (st0 $> t1)
        Array k ss -> st0 $> Array k ss
        IO rw vd s -> st0 $> IO rw vd s

  where t0 = st0 ^. scoped

reduce_ :: Traversal' s Term -> Endom (Scoped s)
reduce_ trv s = trv (reduceTerm . (s $>)) (s ^. scoped)

flatRSession :: Scoped RSession -> [Scoped RSession]
flatRSession ssr
  | Just n <- r1 ^? litR . integral = replicate n (pure $ oneS s)
  | Just (rL,rR) <- r1 ^? addR      = flatRSession (sr1 $> s `Repl` rL)
                                   ++ flatRSession (sr1 $> s `Repl` rR)
  | otherwise                       = [ssr]

  where sr1 = reduce_ rterm (ssr $> r0)
        s   = ssr ^. scoped . rsession
        r0  = ssr ^. scoped . rfactor
        r1  = sr1 ^. scoped

flatSessions :: Endom (Scoped Sessions)
flatSessions ss = sequenceA $ (ss ^. scoped) >>= flatRSession . (ss $>)
