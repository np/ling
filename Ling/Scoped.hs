{-# LANGUAGE TemplateHaskell #-}

module Ling.Scoped (
    allDefs,
    nullDefs,
    mergeDefs,
    addEDef,
    Scoped(Scoped),
    gdefs,
    ldefs,
    scoped,
    subst1,
    scopedName
    ) where

import qualified Data.Map     as Map
import           Prelude      hiding (log)

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Rename
import           Ling.Session

data Scoped a = Scoped { _gdefs, _ldefs :: Defs, _scoped :: a }
  deriving Eq

makeLenses ''Scoped

instance Functor Scoped where
  fmap f (Scoped g l x) = Scoped g l (f x)

  x <$ Scoped g l _ = Scoped g l x

-- Scopes must always be compatible. Namely in a Defs, a given Name always map to the same Term.
instance Applicative Scoped where
  pure = Scoped ø ø
  Scoped gf lf f <*> Scoped gx lx x =
    Scoped (mergeDefs gf gx) (mergeDefs lf lx) (f x)

  Scoped gx lx _ *> Scoped gy ly y =
    Scoped (mergeDefs gx gy) (mergeDefs lx ly) y

  Scoped gx lx x <* Scoped gy ly _ =
    Scoped (mergeDefs gx gy) (mergeDefs lx ly) x

allDefs :: Scoped a -> Defs
allDefs (Scoped g l _) = mergeDefs g l

nullDefs :: Defs -> Bool
nullDefs = Map.null . _defsMap

mergeDefs :: Defs -> Defs -> Defs
mergeDefs = (<>)

instance Monad Scoped where
  return  = pure
  s >>= f = s *> f (s ^. scoped)

instance Dual a => Dual (Scoped a) where
  dual = fmap dual
  log  = fmap log
  sink = fmap sink

scopedName :: Scoped Name -> Maybe (Scoped Term)
scopedName (Scoped g l x) =
  [l, g] ^? each . at x . _Just . annotated . to (Scoped g l)

addEDef :: Name -> Ann (Maybe Typ) Term -> Endom Defs
addEDef x atm m
  | atm ^. annotated == Def x [] = m
  | m ^. hasKey x                = error "addEDef: IMPOSSIBLE"
  | otherwise                    = m & at x ?~ atm

subst1 :: Rename a => Name -> (Name, Ann (Maybe Typ) Term) -> Scoped a -> Scoped a
-- subst1 _ (x, _, Nothing) _ = error $ "Missing type annotation for " ++ unName x
subst1 d (x, atm) _sa@(Scoped gs ls a) =
  case atm ^. annotated of
--    Def y [] -> sa $> rename1 (x, y) a
    _        -> Scoped gs (addEDef x' atm ls) (rename1 (x, x') a)
  where
    x' = prefName (unName d ++ "#") x
