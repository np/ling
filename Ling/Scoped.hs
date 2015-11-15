{-# LANGUAGE TemplateHaskell #-}

module Ling.Scoped (
    Defs,
    mergeDefs,
    addEDef,
    Scoped(Scoped),
    ldefs,
    scoped,
    subst1,
    unDef,
    ) where

import           Data.Map     (insert, member, unionWithKey)
import           Prelude      hiding (log)

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Rename
import           Ling.Session

data Scoped a = Scoped { _ldefs :: Defs, _scoped :: a }
  deriving Eq

$(makeLenses ''Scoped)

instance Functor Scoped where
  fmap f (Scoped d x) = Scoped d (f x)

-- Scopes must always be compatible. Namely in a Defs, a given Name always map to the same Term.
instance Applicative Scoped where
  pure = Scoped ø
  Scoped df f <*> Scoped dx x = Scoped (mergeDefs df dx) (f x) -- error "Scoped (df `union` dx) (f x)"

mergeDefs :: Defs -> Defs -> Defs
mergeDefs = unionWithKey mergeDef
  where mergeDef k v w | v == w    = v
                       | otherwise = error $ "Scoped.mergeDefs: " ++ show k

instance Monad Scoped where
  return = pure
  Scoped dx x >>= f = Scoped (mergeDefs dx dy) y
    where
      Scoped dy y = f x

instance Dual a => Dual (Scoped a) where
  dual = fmap dual
  log  = fmap log
  sink = fmap sink

addEDef :: Name -> Term -> Endom Defs
addEDef x e m
  | e == Def x [] = m
  | x `member` m  = error "addEDef: IMPOSSIBLE"
  | otherwise     = insert x e m

subst1 :: Rename a => Name -> (Name, Term) -> Scoped a -> Scoped a
subst1 d (x, e) (Scoped defs s) =
  Scoped (addEDef x' e defs) (rename1 (x, x') s)
  where
    x' = prefName (unName d ++ "#") x

unDef :: Scoped Name -> Maybe (Scoped Term)
unDef (Scoped defs d) = Scoped defs <$> defs^.at d
                           --  ^^^^ this
-- contains TOO MUCH defs, but one can try
-- to maintain the invariant that renaming happens before inserting in these maps
