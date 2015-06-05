{-# LANGUAGE TemplateHaskell #-}
module Ling.Constraint where

import qualified Data.Set as Set
import Data.Set (Set, insert, union, intersection, singleton, empty,
                 delete, member, isSubsetOf, size, difference)
import Control.Lens
-- import Debug.Trace (trace)

import Ling.Utils

type Constraint  = Set Channel
newtype Constraints = Constraints { _constraintSet :: Set Constraint }

$(makeLenses ''Constraints)

prettyConstraint :: Constraint -> String
prettyConstraint cs = "⦃" ++ pretty (s2l cs) ++ "⦄"

prettyConstraints :: Constraints -> [String]
prettyConstraints = toListOf $ constraintSet . folded . to s2l . to pretty

emptyConstraints :: Constraints
emptyConstraints = Constraints $ Set.singleton empty

noConstraints :: Constraints -> Bool
noConstraints = andOf $ constraintSet . folded . to Set.size . to (< 2)

addConstraint :: [Channel] -> Constraints -> Constraints
addConstraint cs = over constraintSet $ insert (l2s cs)

addConstraints :: [[Channel]] -> Constraints -> Constraints
addConstraints dss = over constraintSet $ union (l2s (map l2s dss))

deleteConstraint :: [Channel] -> Constraints -> Constraints
deleteConstraint cs = over constraintSet $ delete (l2s cs)

-- TODO lens my type
mapConstraints :: (Constraint -> Constraint) -> Constraints -> Constraints
mapConstraints f = over constraintSet ((empty `delete`) . Set.map f)

-- TODO lens my type
filterConstraints :: (Constraint -> Bool) -> Constraints -> Constraints
filterConstraints f = over constraintSet ((empty `delete`) . Set.filter f)

subst :: (Constraint, Constraint) -> Constraint -> Constraint
subst (kx, ky) kz
  | kx `isSubsetOf` kz = (kz `difference` kx) `union` ky
  | otherwise          = kz

subst1 :: (Channel, [Channel]) -> Constraint -> Constraint
subst1 (c, ds) = subst (singleton c, l2s ds)
{- OR
subst1 (c, ds) k
  | c `member` k = (c `delete` k) `union` l2s ds
  | otherwise    = k
-}

subst1If :: Channel -> [Channel] -> Constraints -> Constraints
subst1If c ds ks
  | anyOf (constraintSet . folded) (c `member`) ks = mapConstraints (subst1 (c, ds)) ks
  | otherwise                                      = error "subst1If: IMPOSSIBLE" -- addConstraint ds ks
{-
  | length ds > 1                    = l2s ds : ks
  | otherwise                        = ks
-}

-- TODO: Lens-me
-- TODO: Impure
checkAlone :: Channel -> Constraints -> Constraints
checkAlone c ks
  | singleton c `member` (ks ^. constraintSet) = ks
  | otherwise
      = let Constraints ks' = mapConstraints (c `delete`) (filterConstraints (c `member`) ks) in
        case size ks' of
          0 -> error ("The channel " ++ pretty c ++ " has been re-used or not been introduced")
          1 ->
            let k = s2l (head (s2l ks')) in
            case k of
              []  -> error ("The channel " ++ pretty c ++ " should be used")
              [d] -> error ("The channel " ++ pretty c ++ " should be used independantly from channel " ++ pretty d)
              _   ->
                error
                 $ "The channel " ++ pretty c ++ " should be used independantly from channels " ++ pretty k
          _ -> error "checkAlone: IMPOSSIBLE"

limitConstraintTo :: Set Channel -> Constraint -> Constraint
limitConstraintTo cs k = k `intersection` cs

limitConstraintsTo :: Set Channel -> Constraints -> Constraints
limitConstraintsTo = mapConstraints . limitConstraintTo

prettyConstraints' :: Constraints -> String
prettyConstraints' ks = "⦃" ++ concat (prettyConstraints ks) ++ "⦄"

{-
splitConstraints :: Constraints -> Constraint -> Constraints
splitConstraints ks k =
--  trace ("splitConstraints(" ++ prettyConstraints' ks ++ ", " ++ prettyConstraint k ++ ") = " ++ prettyConstraints' res) res where
-- res =
  filterConstraints (`isSubsetOf` k) ks
{-
  case ks ^.. to (filterConstraints (`isSubsetOf` k)) . constraintSet . folded of
    []  -> Nothing
    [x] | Set.null x -> error "splitConstraints: impossible, empty constraint"
        | otherwise  -> Just x
    _   -> trace "splitConstraints: impossible" Nothing
-}

data ConstraintStatus = CLeft | CRight | CSplit | CError String
  deriving (Eq,Show)

isCError :: ConstraintStatus -> Bool
isCError CError{} = True
isCError _        = False

prettyCCS :: (Constraint, ConstraintStatus) -> String
prettyCCS (cs, st) = prettyConstraint cs ++ " " ++ show st

prettyMCCS :: Map Constraint ConstraintStatus -> [String]
prettyMCCS = map prettyCCS . m2l

mergeConstraint :: Constraints -> Constraints -> Constraint -> ConstraintStatus
mergeConstraint ks0 ks1 k =
  case (ks0k, ks1k) of
    ([], []) -> CError "mergeConstraint: impossible 1"
    (_,  []) -> CLeft
    ([],  _) -> CRight
    ([k0], [k1])
       | k0 == k && k1 == k     -> CError "mergeConstraints: impossible 2"
       | k0 == k && Set.null k1 -> CError "mergeConstraints: impossible 3"
       | k1 == k && Set.null k0 -> CError "mergeConstraints: impossible 4"
       | k0 `union` k1 == k     -> CSplit
       | otherwise              -> CError "mergeConstraints: impossible 5"
    _ -> CError "mergeConstraints: impossible 6"
  where
    ks0k = splitConstraints ks0 k ^.. constraintSet . folded
    ks1k = splitConstraints ks1 k ^.. constraintSet . folded

mergeConstraints :: Constraints -> Constraints -> Constraints -> Map Constraint ConstraintStatus
mergeConstraints ks0 ks1 (Constraints ks01) =
  l2m (map (\k -> (k, mergeConstraint ks0 ks1 k)) . filter (not . Set.null) $ s2l ks01)
-}
