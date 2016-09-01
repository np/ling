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

-- If one considers this layer of definitions to be local definitions.
unScopedTerm :: Scoped Term -> Term
unScopedTerm (Scoped _ defs t) = mkLet defs t
-- TODO

reduceL :: Scoped Term -> Term
reduceL = mkLetS . view reduced . reduce
