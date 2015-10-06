module Ling.Constraint
  ( Constraint
  , Constraints
  , constraintSet
  , eachConstraint
  , noConstraints
  , constrainChan
  , unconstrainChan
  , singleConstraint
  , prettyConstraints
  , constrainPrllChans
  ) where

import Prelude hiding (null)

import Control.Lens
import Data.Set (Set, null, insert, union, unions, empty, delete)
import Data.Set.Lens (setmapped)

import Ling.Print
import Ling.Utils

type Constraint  = Set Channel

-- Invariant: the empty set should always be a member of the 'Set Constraint'
newtype Constraints = MkConstraints { _constraintSet :: Set Constraint }
  deriving (Eq)

mkConstraints :: Set Constraint -> Constraints
mkConstraints cs | null cs   = ø
                 | otherwise = MkConstraints $ delete empty cs

instance Monoid Constraints where
  mempty = MkConstraints $ l2s [empty]
  mappend (MkConstraints s0) (MkConstraints s1) =
    mkConstraints $ s0 `union` s1
  mconcat = mkConstraints . unions . map _constraintSet

constraintSet :: Lens' Constraints (Set Constraint)
constraintSet f (MkConstraints xs) = mkConstraints <$> f xs

eachConstraint :: Setter' Constraints Constraint
eachConstraint = constraintSet . setmapped

prettyConstraints :: Constraints -> [String]
prettyConstraints = toListOf $ constraintSet . folded . to pretty

singleConstraint :: Constraint -> Constraints
singleConstraint = MkConstraints . l2s . pure

noConstraints :: Constraints -> Bool
noConstraints = (== ø)

constrainChan :: Channel -> Constraints -> Constraints
constrainChan c = eachConstraint %~ insert c

unconstrainChan :: Channel -> Constraints -> Constraints
unconstrainChan c = eachConstraint %~ delete c

constrainPrllChans :: [Channel] -> Constraints -> Constraints
constrainPrllChans cs constraints =
  mconcat $ map (`constrainChan` constraints) cs
