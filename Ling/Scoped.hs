{-# LANGUAGE TemplateHaskell #-}
module Ling.Scoped
  ( Sub
  , Defs
  , emptyScope
  , addEDef
  , Scoped(Scoped)
  , ldefs
  , scoped
  , subst1
  , unDef
  )
  where

import           Control.Lens
import           Data.Map     (Map, insert, member)
import           Prelude      hiding (log)

import           Ling.Norm
import           Ling.Rename
import           Ling.Session
import           Ling.Utils   hiding (subst1)

type Sub  = Map Name Term
type Defs = Sub

data Scoped a = Scoped
  { _ldefs  :: Defs
  , _scoped :: a
  }
  deriving (Eq)

$(makeLenses ''Scoped)

instance Functor Scoped where
  fmap f (Scoped d x) = Scoped d (f x)

{- Maybe ...
instance Applicative Scoped where
  pure = Scoped Map.empty
  Scoped df f <*> Scoped dx x = ...
-}

emptyScope :: a -> Scoped a
emptyScope = Scoped ø

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
subst1 d (x,e) (Scoped defs s) =
  Scoped (addEDef x' e defs) (rename1 (x,x') s)
  where
    x'  = prefName (unName d ++ "#") x

unDef :: Scoped Name -> Maybe (Scoped Term)
unDef (Scoped defs d) = Scoped defs <$> defs^.at d
                           --  ^^^^ this
-- contains TOO MUCH defs, but one can try
-- to maintain the invariant that renaming happens before inserting in these maps
