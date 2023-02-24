{-# LANGUAGE TemplateHaskell #-}

module Ling.Scoped (
    allDefs,
    nullDefs,
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
import           Ling.Session.Core

data Scoped a = Scoped { _gdefs, _ldefs :: Defs, _scoped :: a }
  deriving (Eq, Show)

makeLenses ''Scoped

instance Semigroup a => Semigroup (Scoped a) where
  Scoped gx lx x <> Scoped gy ly y =
    Scoped (gx <> gy) (lx <> ly) (x <> y)

instance Monoid a => Monoid (Scoped a) where
  mempty = Scoped ø ø ø

instance Functor Scoped where
  fmap f (Scoped g l x) = Scoped g l (f x)

  x <$ Scoped g l _ = Scoped g l x

-- Scopes must always be compatible. Namely in a Defs, a given Name always map to the same Term.
instance Applicative Scoped where
  pure = Scoped ø ø
  Scoped gf lf f <*> Scoped gx lx x =
    Scoped (gf <> gx) (lf <> lx) (f x)

  Scoped gx lx _ *> Scoped gy ly y =
    Scoped (gx <> gy) (lx <> ly) y

  Scoped gx lx x <* Scoped gy ly _ =
    Scoped (gx <> gy) (lx <> ly) x

allDefs :: Scoped a -> Defs
allDefs (Scoped g l _) = g <> l

nullDefs :: Defs -> Bool
nullDefs = Map.null . _defsMap

instance Monad Scoped where
  return  = pure
  s >>= f = s *> f (s ^. scoped)

instance Dual a => Dual (Scoped a) where
  sessionOp = fmap . sessionOp
  dual      = fmap dual
  log       = fmap log
  isMaster  = isMaster . view scoped

scopedName :: Scoped Name -> Maybe (Scoped Term)
scopedName (Scoped g l x) =
  [l, g] ^? each . at x . _Just . annotated . to (Scoped g l)

subst1 :: Rename s => (Name, Ann (Maybe Typ) Term) -> s -> Scoped s
subst1 (x, Ann mty tm) s
  | x == anonName = pure s
  | otherwise =
  case tm of
    Def _ y [] | isInternalName y ->
      pure $ rename1I (x, y) s
    _ ->
      let (hx, hmty, htm) = hDef x mty tm in
      Scoped ø (aDef hx hmty htm) (rename1I (x, hx) s)
