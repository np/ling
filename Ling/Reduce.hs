{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.Reduce where

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Proc
import           Ling.Scoped
import           Ling.Session

-- If one considers this layer of definitions to be local definitions.
unScopedTerm :: Scoped Term -> Term
unScopedTerm (Scoped _ defs t) = mkLet defs t

app :: Name -> Scoped Term -> [Term] -> Scoped Term
app d st0 = \case
  []     -> st1
  (u:us) ->
    case st1 ^. scoped of
      Lam (Arg x _) t2 -> app d (subst1 d (x, u) (st1 $> t2)) us
      Def x es         -> st1 $> Def x (es ++ u : us)
      _                -> error "Ling.Reduce.app: IMPOSSIBLE"

  where st1 = reduceTerm st0

reduceCase :: Scoped Term -> [Branch] -> Scoped Term
reduceCase st0 brs =
  case st1 ^. scoped of
    Con{} -> reduceTerm scase
    _     -> scase

  where st1   = reduceTerm st0
        scase = (`mkCase` brs) <$> st1

pushLetSession :: Scoped Session -> Session
pushLetSession s0 = case s0 ^. scoped of
  TermS p t  -> termS p $ pushLetTerm (s0 $> t)
  Array k ss -> Array k $ mkLet_ (list . rSessionTerms) (s0 $> ss)
  IO rw vd s -> uncurry (IO rw) $
                  mkLet_ (varDecTerms `beside` sessionTerms) (s0 $> (vd, s))

reduceDef :: Scoped Name -> [Term] -> Scoped Term
reduceDef sd es
  | Just st <- scopedName sd = app d st es
  | otherwise                = sd $> Def d es

  where d = sd ^. scoped

reduceTerm :: Scoped Term -> Scoped Term
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

pushLetTerm :: Scoped Term -> Term
pushLetTerm st0 = case st0 ^. scoped of
  Let defs t   -> pushLetTerm (st0 *> Scoped ø defs t)
  Lit l        -> Lit l
  TTyp         -> TTyp
  Con n        -> Con n
  Def{}        -> unScopedTerm st0 -- this might leave a let
  Case t brs   -> uncurry Case $ mkLet_ (id `beside` branches) (st0 $> (t, brs))
  Lam arg t    -> uncurry Lam $ mkLet_ absTerms (st0 $> (arg, t))
  Proc cs p    -> Proc (mkLet_ (list . chanDecTerms) (st0 $> cs)) (mkLetProc (st0 $> p))
  TFun arg s   -> uncurry TFun $ mkLet_ absTerms (st0 $> (arg, s))
  TSig arg s   -> uncurry TSig $ mkLet_ absTerms (st0 $> (arg, s))
  TProto ss    -> TProto $ mkLet_ (list . rSessionTerms) (st0 $> ss)
  TSession s   -> pushLetSession (st0 $> s) ^. tSession

-- TODO: Avoid useless `LetA`s (either nested or empty)
mkLetProc :: Scoped Proc -> Proc
mkLetProc (Scoped _ defs p) = LetA defs `actP` [p]

sessionTerms :: Traversal' Session Term
sessionTerms f = \case
  TermS p t  -> termS p <$> f t
  Array k ss -> Array k <$> (list . rSessionTerms) f ss
  IO rw vd s -> IO rw <$> varDecTerms f vd <*> sessionTerms f s

rSessionTerms :: Traversal' RSession Term
rSessionTerms f (s `Repl` RFactor r) = Repl <$> sessionTerms f s <*> (RFactor <$> f r)

varDecTerms :: Traversal' VarDec Term
varDecTerms = argTerms _Just

absTerms :: Traversal' (VarDec, Term) Term
absTerms = varDecTerms `beside` id

chanDecTerms :: Traversal' ChanDec Term
chanDecTerms = argTerms (_Just . rSessionTerms)

-- ideally would be with traversals indexed by the names to avoid
argTerms :: Traversal' a Term -> Traversal' (Arg a) Term
argTerms trv f (Arg x b) = Arg x <$> trv f b

mkLet :: Defs -> Term -> Term
mkLet defs0 = \case
  Lit l               -> Lit l
  Con n               -> Con n
  TTyp                -> TTyp
  t0 | nullDefs defs0 -> t0
  Def d []            -> fromMaybe (Def d []) (defs0 ^. at d)
  Let defs1 t1        -> mkLet (mergeDefs defs0 defs1) t1
  t0@Def{}            -> Let defs0 t0
  t0@Lam{}            -> Let defs0 t0
  t0@Case{}           -> Let defs0 t0
  t0@Proc{}           -> Let defs0 t0
  t0@TFun{}           -> Let defs0 t0
  t0@TSig{}           -> Let defs0 t0
  t0@TProto{}         -> Let defs0 t0
  t0@TSession{}       -> Let defs0 t0

-- Short-cutting the traversal when defs is null requires s ~ t
mkLet_ :: Traversal s t Term Term -> Scoped s -> t
mkLet_ trv s = (s ^. scoped) & trv %~ mkLet (s ^. ldefs)

reduce_ :: Traversal' s Term -> Scoped s -> Scoped s
reduce_ trv s = trv (reduceTerm . (s $>)) (s ^. scoped)

flatRSession :: Scoped RSession -> [Scoped RSession]
flatRSession ssr =
  case () of
  _ | Just n <- isLitR r1       -> replicate (fromInteger n) (pure $ oneS s)
  _ | Just (rL,rR) <- isAddR r1 -> flatRSession (sr1 $> s `Repl` rL)
                                ++ flatRSession (sr1 $> s `Repl` rR)
  _                             -> [ssr]
  where sr1 = reduce_ rterm (ssr $> r0)
        s   = ssr ^. scoped . rsession
        r0  = ssr ^. scoped . rfactor
        r1  = sr1 ^. scoped

flatSessions :: Scoped Sessions -> Scoped Sessions
flatSessions ss = sequenceA $ (ss ^. scoped) >>= flatRSession . (ss $>)
