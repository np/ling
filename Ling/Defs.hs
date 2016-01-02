{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.Defs where

import Ling.Norm
import Ling.Prelude
import Ling.Scoped
import Ling.Session
import Ling.SubTerms

mkLet :: Defs -> Endom Term
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

mkLet__ :: SubTerms a => Scoped a -> a
mkLet__ = mkLet_ subTerms

pushDefs__ :: PushDefs a => ASetter s t a a -> Scoped s -> t
pushDefs__ l ss = (ss ^. scoped) & l %~ pushDefs . (ss $>)

-- If one considers this layer of definitions to be local definitions.
unScopedTerm :: Scoped Term -> Term
unScopedTerm (Scoped _ defs t) = mkLet defs t

class PushDefs a where
  pushDefs :: Scoped a -> a

instance PushDefs a => PushDefs [a] where
  pushDefs = pushDefs__ list

instance PushDefs a => PushDefs (Prll a) where
  pushDefs = pushDefs__ unPrll

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
      Case t brs   -> _Case # mkLet_ (id `beside` branches) (st0 $> (t, brs))
      Proc cs p    -> Proc (mkLet__ (st0 $> cs)) (pushDefs (st0 $> p))
      Lam  arg t   -> _Lam  # mkLet_ absTerms (st0 $> (arg, t))
      TFun arg t   -> _TFun # mkLet_ absTerms (st0 $> (arg, t))
      TSig arg t   -> _TSig # mkLet_ absTerms (st0 $> (arg, t))
      TProto ss    -> TProto $ mkLet__ (st0 $> ss)
      TSession s   -> pushDefs (st0 $> s) ^. tSession

instance PushDefs RSession where
  pushDefs = mkLet__

instance PushDefs Session where
  pushDefs s0 =
    case s0 ^. scoped of
      TermS p t  -> termS p $ pushDefs (s0 $> t)
      Array k ss -> Array k $ mkLet__ (s0 $> ss)
      IO rw vd s -> uncurry (IO rw) $
                      mkLet_ (varDecTerms `beside` subTerms) (s0 $> (vd, s))

instance PushDefs Proc where
  pushDefs sp0 =
    case sp0 ^. scoped of
      Act act -> Act (pushDefs (sp0 $> act))
      Procs procs -> Procs (pushDefs (sp0 $> procs))
      NewSlice cs t x proc0 -> NewSlice cs (mkLet__ (sp0 $> t)) x (pushDefs (sp0 $> proc0))
      proc0 `Dot` proc1 ->
        case proc0 of
          Act (LetA defs) -> Act (LetA (sp0 ^. ldefs <> defs)) `Dot` proc1
          _ -> Act (LetA (sp0 ^. ldefs)) `Dot` proc0 `Dot` proc1

instance PushDefs Act where
  pushDefs sa =
    case sa ^. scoped of
      Split k c ds    -> Split k c $ mkLet__ (sa $> ds)
      Send c e        -> Send c $ mkLet_ id (sa $> e)
      Recv c arg      -> Recv c $ mkLet_ varDecTerms (sa $> arg)
      Nu anns newpatt -> Nu (mkLet_ list (sa $> anns)) (mkLet__ (sa $> newpatt))
      LetA{}          -> error "`let` is not supported in parallel actions (pushDefs)"
      Ax s cs         -> _Ax # mkLet_ (subTerms `beside` ignored) (sa $> (s, cs))
      At t pat        -> _At # mkLet_ (id `beside` subTerms) (sa $> (t, pat))
