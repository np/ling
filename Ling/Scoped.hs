{-# LANGUAGE TemplateHaskell #-}
module Ling.Scoped
  ( Sub
  , Defs
  , addEDef
  , Scoped(Scoped)
  , ldefs
  , scoped
  , subst1
  , app
  , unDef
  )
  where

import           Control.Lens
import           Data.Map     (Map)
import qualified Data.Map     as Map
import           Data.Maybe   (fromMaybe)

import           Ling.Abs     (Name)
import           Ling.Norm
import           Ling.Rename
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

addEDef :: Name -> Term -> Endom Defs
addEDef x e m
  | e == Def x []    = m
  | x `Map.member` m = error "addEDef: IMPOSSIBLE"
  | otherwise        = Map.insert x e m

subst1 :: Rename a => Name -> (Name, Term) -> Scoped a -> Scoped a
subst1 d (x,e) (Scoped defs s) =
  Scoped (addEDef x' e defs) (rename1 (x,x') s)
  where
    x'  = prefName (unName d ++ "#") x

app :: Name -> Scoped Term -> [Term] -> Scoped Term
app _ t []     = unDef t
app d t (u:us) =
  case unDef t of
    Scoped defs (Lam (Arg x _) t') ->
      app d (subst1 d (x,u) (Scoped defs t')) us
    Scoped defs (Def x es) ->
      Scoped defs $ Def x (es ++ u:us)
    _                -> error "Ling.Subst.app: IMPOSSIBLE"

unDef :: Scoped Term -> Scoped Term
unDef s@(Scoped defs t) =
  case t of
    Def d es -> fromMaybe s (app d <$> (Scoped defs <$> defs ^. at d) <*> pure es)
                                           --  ^^^^ TOO MUCH, but one can try
    -- to maintain the invariant that renaming happens before inserting in these maps
    _        -> s
