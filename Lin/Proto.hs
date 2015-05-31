{-# LANGUAGE TemplateHaskell #-}
module Lin.Proto where

import Prelude hiding (log)
import Lin.Utils
import Lin.Constraint
import Lin.Session
import Lin.Norm
import Lin.Print.Instances ()

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Lens

-- These constraints are solved!
data Proto = MkProto { _chans       :: Map Channel Session
                     , _constraints :: Constraints
                     , _orders      :: [[Channel]]
                     }

$(makeLenses ''Proto)

prettyProto :: Proto -> [String]
prettyProto p =
  [" channels:"] ++ prettyChanDecs p
  ++
  if p ^. constraints . to noConstraints then [] else
  " constraints:"
  : map ("  " ++) (prettyConstraints (p ^. constraints))
  ++
  if p ^. orders . to null then [] else
  " orders:"
  : map ("  " ++) (map (show . map unName) (p ^. orders))

chanDecs :: Proto -> [Arg Session]
chanDecs p = p ^.. chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = prettyList . chanDecs

emptyProto :: Proto
emptyProto = MkProto Map.empty emptyConstraints []

chanPresent :: Proto -> Channel -> Bool
chanPresent p c = has (chans . at c . _Just) p

isEmptyProto :: Proto -> Bool
isEmptyProto p = p ^. chans . to Map.null

addChanOnly :: (Channel,Session) -> Proto -> Proto
addChanOnly (c,s) = chans  %~ at c .~ Just s

data ConstraintFlag = WithConstraint | WithoutConstraints

addChanConstraint :: ConstraintFlag -> Channel -> Proto -> Proto
addChanConstraint WithoutConstraints _ = id
addChanConstraint WithConstraint     c = constraints %~ mapConstraints (c `Set.insert`)

addChan :: ConstraintFlag -> (Channel,Session) -> Proto -> Proto
addChan flag (c,s) = addChanOnly (c,s) . addChanConstraint flag c

addChans :: ConstraintFlag -> [(Channel,Session)] -> Proto -> Proto
addChans flag = flip (foldr (addChan flag))

addChanWithOrder :: (Channel,Session) -> Proto -> Proto
addChanWithOrder (c,s) p = p & addChan WithConstraint (c,s)
                             & orders %~ addOrder
  where addOrder []   = [[c]]
        addOrder [cs] = [c:cs]
        addOrder _css = error "addChanWithOrder: TODO"
           -- TODO: if we do
           -- map (c:) css
           -- then substChans will complain about the extra 'c' everywhere...

rmChanAndConstraint :: Channel -> Proto -> Proto
rmChanAndConstraint c p =
  p & chans . at c .~ Nothing
    & constraints %~ mapConstraints (c `Set.delete`)
            --   & orders . mapped %~ filter (/= c)

rmChansAndConstraints :: [Channel] -> Proto -> Proto
rmChansAndConstraints = flip (foldr rmChanAndConstraint)

rmChan :: Channel -> Proto -> Proto
rmChan c p =
  p & rmChanAndConstraint c
    & orders . mapped %~ filter (/= c)

rmChans :: [Channel] -> Proto -> Proto
rmChans = flip (foldr rmChan)

-- TODO write quickcheck props about this function
substList :: Ord a => (Set a,[a]) -> [a] -> Maybe [a]
substList (xs,ys) zs
  | Set.null xs           = Just $ ys  ++ zs
  | null zs1              = Just   zs0
  | xs == xs' && null zs5 = Just $ zs0 ++ ys ++ zs4
  | otherwise             = Nothing
    where
      (zs0,zs1) = break (`Set.member` xs) zs
      (zs2,zs3) = span  (`Set.member` xs) zs1
      (zs4,zs5) = break (`Set.member` xs) zs3
      xs'       = l2s zs2

substChans :: ConstraintFlag -> ([Channel], [(Channel,Session)]) -> Proto -> Maybe Proto
substChans flag (cs, css) p =
  p & orders . each %%~ substList (l2s cs, map fst css)
   <&> rmChansAndConstraints cs
   <&> addChans flag css

chanSession :: Channel -> Proto -> Maybe Session
chanSession c p = p ^. chans . at c

chanSessions :: [Channel] -> Proto -> [Maybe Session]
chanSessions cs p = map (`chanSession` p) cs

mkProto :: [(Channel,Session)] -> Proto
mkProto css = MkProto (l2m css) (Constraints (l2s [l2s cs]))
                      (map return cs)
  where cs = map fst css

protoAx :: Session -> Channel -> Channel -> [Channel] -> Proto
protoAx s c d es = mkProto ((c,s):(d,dual s):map (\e -> (e, log s)) es)

replProto :: Term -> Proto -> Proto
replProto n = chans . mapped %~ replSessionTerm n
-- -}
