{-# LANGUAGE TemplateHaskell #-}

module Ling.Scoped (
    allDefs,
    nullDefs,
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
import           Ling.Print
import           Ling.Rename
import           Ling.Session

data Scoped a = Scoped { _gdefs, _ldefs :: Defs, _scoped :: a }
  deriving Eq

makeLenses ''Scoped

instance Monoid a => Monoid (Scoped a) where
  mempty = Scoped ø ø ø
  Scoped gx lx x `mappend` Scoped gy ly y =
    Scoped (gx <> gy) (lx <> ly) (x <> y)

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
  dualOp = fmap . dualOp
  dual   = fmap dual
  log    = fmap log
  sink   = fmap sink
  isLog  = isLog  . view scoped
  isSink = isSink . view scoped

instance Print a => Print (Scoped a) where
  prt i (Scoped _ ld x)
    -- the global scope is not displayed
    | nullDefs ld = prt i x
    | otherwise   =
        concatD [ doc (showString "let ") , prt 0 ld
                , doc (showString "in")
                , prt i x ]

scopedName :: Scoped Name -> Maybe (Scoped Term)
scopedName (Scoped g l x) =
  [l, g] ^? each . at x . _Just . annotated . to (Scoped g l)

addEDef :: Name -> Ann (Maybe Typ) Term -> Endom Defs
addEDef x atm m
  | atm ^. annotated == Def x [] = m
  | m ^. hasKey x                = error $ "addEDef: IMPOSSIBLE " ++ pretty (x, atm, m)
  | otherwise                    = m & at x ?~ atm

subst1 :: Rename a => Name -> (Name, Ann (Maybe Typ) Term) -> Endom (Scoped a)
-- subst1 _ (x, _, Nothing) _ = error $ "Missing type annotation for " ++ unName x
subst1 d (x, atm) _sa@(Scoped gs ls a) =
  case atm ^. annotated of
--    Def y [] -> sa $> rename1 (x, y) a
    _        -> Scoped gs (addEDef x' atm ls) (rename1 (x, x') a)
  where
    x' = prefixedName (unName d ++ "#") # x
