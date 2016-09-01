{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Ling.Defs where

import Ling.Norm
import Ling.Prelude
import Ling.Proc
import Ling.Reduce
import Ling.Scoped
--import Ling.Session.Core
import Ling.SubTerms

{-
  This function is a smart-constructor for `Let`, it tries to not create a useless
  `Let` node. Moreover it can push the created `Let` further down the tree if it
  is guaranteed that only one part could need it.
  Finally it is guaranteed that at most one `Let` will be created.
-}
mkLet :: Defs -> Endom Term
mkLet defs0 t0 = case t0 of
  Lit{}              -> t0
  Con{}              -> t0
  TTyp               -> t0
  _ | nullDefs defs0 -> t0
  -- Let defs1 t1       -> mkLet (defs0 <> defs1) t1
  -- ^ This causes some let's to be printed out of order as we have no
  -- syntax for multiple local definitions.
  Let{}              -> lt0
  Lam{}              -> lt0
  Case e []          -> Case (mkLet defs0 e) []
  Case{}             -> lt0
  Proc [] p          -> Proc [] $ defs0 `dotP` p
  Proc{}             -> lt0
  TFun{}             -> lt0
  TSig{}             -> lt0
  TProto{}           -> lt0
  TSession{}         -> lt0
  Def k d es         ->
    case es of
      [] ->
        case defs0 ^? at d . _Just . annotated of
          Just t1 -> mkLet defs0 t1
          _       -> t0
      [e]
        | defs0 & has (at d . _Just) -> lt0
        | otherwise                  -> Def k d [mkLet defs0 e]
      _ -> lt0

  where lt0 = Let defs0 t0

-- Same as `mkLet` but takes a `Scoped Term`.
mkLetS :: Scoped Term -> Term
mkLetS s = mkLet (s ^. ldefs) (s ^. scoped)

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

pushDefsR :: PushDefs a => Reduced a -> a
pushDefsR = pushDefs . view reduced

reduceP :: (HasReduce a b, PushDefs b) => Scoped a -> b
reduceP = pushDefsR . reduce

reduceL :: Scoped Term -> Term
reduceL = mkLetS . view reduced . reduce

class PushDefs a where
  pushDefs :: Scoped a -> a

instance PushDefs a => PushDefs (Maybe a) where
  pushDefs = pushDefs__ _Just

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
      Def k d es   -> warn k d es (Def k d (pushDefs (st0 $> es)))
      Case t brs   -> _Case # mkLet_ (id `beside` branches) (st0 $> (t, brs))
      Proc cs p    -> Proc (mkLet__ (st0 $> cs)) (st0 ^. ldefs `dotP` p)
      Lam  arg t   -> _Lam  # mkLet_ absTerms (st0 $> (arg, t))
      TFun arg t   -> _TFun # mkLet_ absTerms (st0 $> (arg, t))
      TSig arg t   -> _TSig # mkLet_ absTerms (st0 $> (arg, t))
      TProto ss    -> TProto $ mkLet__ (st0 $> ss)
      TSession s   -> pushDefs (st0 $> s) ^. tSession
    where
      warn Defined d []
        | Just e <- allDefs st0 ^? at d . _Just . annotated
        , e /= Def Undefined d []
        = trace $ "[WARNING] PushDefs Term: pushDefs should be called on reduced terms but " ++ show d ++ " has a definition"
      warn _ _ _ = id

{-
instance PushDefs RSession where
  pushDefs = mkLet__
-}

instance PushDefs Session where
  pushDefs = mkLet__
{-
  pushDefs s0 =
    case s0 ^. scoped of
      TermS p t  -> termS p $ pushDefs (s0 $> t)
      Array k ss -> Array k $ mkLet__ (s0 $> ss)
      IO rw vd s -> uncurry (IO rw) $
                      mkLet_ (varDecTerms `beside` subTerms) (s0 $> (vd, s))
-}

instance PushDefs Proc where
  pushDefs sp0 =
    case sp0 ^. scoped of
      Act act -> Act . pushDefs $ sp0 $> act
      Procs procs -> Procs . pushDefs $ sp0 $> procs
      NewSlice cs t x proc0 -> NewSlice cs (mkLet__ (sp0 $> t)) x . pushDefs $ sp0 $> proc0
      Dot{} -> sp0 ^. ldefs `dotP` sp0 ^. scoped
      LetP defs p -> pushDefs $ sp0 *> Scoped ø defs p

instance PushDefs Act where
  pushDefs sa =
    case sa ^. scoped of
      Split c pat     -> Split c $ mkLet__ (sa $> pat)
      Send c os e     -> uncurry (Send c) $ mkLet_ (subTerms `beside` id) (sa $> (os, e))
      Recv c arg      -> Recv c $ mkLet_ varDecTerms (sa $> arg)
      Nu anns newpatt -> Nu (mkLet_ list (sa $> anns)) (mkLet__ (sa $> newpatt))
      Ax s cs         -> _Ax # mkLet_ (subTerms `beside` ignored) (sa $> (s, cs))
      At t pat        -> _At # mkLet_ (id `beside` subTerms) (sa $> (t, pat))

instance (PushDefs a, PushDefs b) => PushDefs (Ann a b) where
  pushDefs sxy =
    case sxy ^. scoped of
      Ann x y -> Ann (pushDefs (sxy $> x)) (pushDefs (sxy $> y))

instance PushDefs a => PushDefs (Arg a) where
  pushDefs = pushDefs__ argBody

instance PushDefs Defs where
  pushDefs = pushDefs__ each

instance PushDefs ChanDec where
  pushDefs scd =
    case scd ^. scoped of
      ChanDec c r ms -> ChanDec c (mkLet__ (scd $> r)) (mkLet__ (scd $> ms))

instance PushDefs RFactor where
  pushDefs = pushDefs__ _RFactor
