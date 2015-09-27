module Ling.Constraint
  ( Constraint
  , Constraints
  , constraintSet
  , eachConstraint
  , noConstraints
  , emptyConstraints
  , constrainChan
  , unconstrainChan
  , singleConstraint
  , mergeConstraints
  , prettyConstraint
  , prettyConstraints
  ) where

import Prelude hiding (null)

import Control.Lens
import Data.Set (Set, insert, union, empty, delete)
import Data.Set.Lens (setmapped)

import Ling.Print (pretty)
import Ling.Utils (Channel,l2s,s2l)

type Constraint  = Set Channel

-- Invariant: the empty set should always be a member of the 'Set Constraint'
newtype Constraints = MkConstraints { _constraintSet :: Set Constraint }
  deriving (Eq)

constraintSet :: Lens' Constraints (Set Constraint)
constraintSet f (MkConstraints xs) = MkConstraints . insert empty <$> f xs

eachConstraint :: Setter' Constraints Constraint
eachConstraint = constraintSet . setmapped

prettyConstraint :: Constraint -> String
prettyConstraint cs = "⦃" ++ pretty (s2l cs) ++ "⦄"

prettyConstraints :: Constraints -> [String]
prettyConstraints = toListOf $ constraintSet . folded . to s2l . to pretty

emptyConstraints :: Constraints
emptyConstraints = MkConstraints $ l2s [empty]

singleConstraint :: Set Channel -> Constraints
singleConstraint cs = MkConstraints $ l2s [empty, cs]

noConstraints :: Constraints -> Bool
noConstraints = (== emptyConstraints)

mergeConstraints :: Constraints -> Constraints -> Constraints
mergeConstraints (MkConstraints c0) (MkConstraints c1) =
  MkConstraints $ c0 `union` c1

constrainChan :: Channel -> Constraints -> Constraints
constrainChan c = over eachConstraint (insert c)

unconstrainChan :: Channel -> Constraints -> Constraints
unconstrainChan c = over eachConstraint (delete c)
