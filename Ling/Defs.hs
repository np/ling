{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.Defs where

import Ling.Norm
import Ling.Prelude
import Ling.Scoped
import Ling.Session
import Ling.SubTerms

mkLet :: Defs -> Term -> Term
mkLet defs0 = \case
  Lit l               -> Lit l
  Con n               -> Con n
  TTyp                -> TTyp
  t0 | nullDefs defs0 -> t0
  Def d []            -> defs0 ^? at d . _Just . annotated ?| Def d []
  Let defs1 t1        -> mkLet (defs0 <> defs1) t1
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

-- If one considers this layer of definitions to be local definitions.
unScopedTerm :: Scoped Term -> Term
unScopedTerm (Scoped _ defs t) = mkLet defs t

class PushDefs a where
  pushDefs :: Scoped a -> a

instance PushDefs a => PushDefs [a] where
  pushDefs sxs = pushDefs . (sxs $>) <$> sxs ^. scoped

instance (PushDefs a, PushDefs b) => PushDefs (a, b) where
  pushDefs sxy =
    case sxy ^. scoped of
      (x, y) -> (pushDefs (sxy $> x), pushDefs (sxy $> y))

instance PushDefs Term where
  pushDefs st0 =
    case st0 ^. scoped of
      Let defs t   -> pushDefs (st0 *> Scoped ø defs t)
      Lit l        -> Lit l
      TTyp         -> TTyp
      Con n        -> Con n
      Def{}        -> unScopedTerm st0 -- this might leave a let
      Case t brs   -> uncurry Case $ mkLet_ (id `beside` branches) (st0 $> (t, brs))
      Lam arg t    -> uncurry Lam $ mkLet_ absTerms (st0 $> (arg, t))
      Proc cs p    -> Proc (mkLet_ subTerms (st0 $> cs)) (pushDefs (st0 $> p))
      TFun arg s   -> uncurry TFun $ mkLet_ absTerms (st0 $> (arg, s))
      TSig arg s   -> uncurry TSig $ mkLet_ absTerms (st0 $> (arg, s))
      TProto ss    -> TProto $ mkLet_ (list . subTerms) (st0 $> ss)
      TSession s   -> pushDefs (st0 $> s) ^. tSession

instance PushDefs Session where
  pushDefs s0 =
    case s0 ^. scoped of
      TermS p t  -> termS p $ pushDefs (s0 $> t)
      Array k ss -> Array k $ mkLet_ (list . subTerms) (s0 $> ss)
      IO rw vd s -> uncurry (IO rw) $
                      mkLet_ (varDecTerms `beside` subTerms) (s0 $> (vd, s))

instance PushDefs Proc where
  pushDefs sp0 =
    case sp0 ^. scoped of
      acts `Dot` procs ->
        case acts of
          [LetA defs] ->
            mconcat $ pushDefs (sp0 *> Scoped ø defs procs)
          _ ->
            uncurry Dot $ pushDefs (sp0 $> (acts, procs))

instance PushDefs Act where
  pushDefs sa =
    case sa ^. scoped of
      Split k c ds    -> Split k c $ mkLet_ subTerms (sa $> ds)
      Send c e        -> Send c $ mkLet_ id (sa $> e)
      Recv c arg      -> Recv c $ mkLet_ varDecTerms (sa $> arg)
      Nu c d          -> uncurry Nu $ mkLet_ subTerms (sa $> (c, d))
      NewSlice cs t x -> NewSlice cs (mkLet_ rterm (sa $> t)) x
      LetA{}          -> error "`let` is not supported in parallel actions (pushLetAct)"
      Ax s cs         -> uncurry Ax $ mkLet_ (subTerms `beside` ignored) (sa $> (s, cs))
      At t pat        -> uncurry At $ mkLet_ (id `beside` subTerms) (sa $> (t, pat))
