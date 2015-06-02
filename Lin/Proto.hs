{-# LANGUAGE TemplateHaskell #-}
module Lin.Proto where

import Prelude hiding (log)
import Lin.Utils
import Lin.Constraint
import Lin.Session
import Lin.Norm
import Lin.Print.Instances ()

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Lens

-- These constraints are solved!
data Proto = MkProto { _chans       :: Map Channel RSession
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
  : map (("  " ++) . show . map unName) (p ^. orders)

chanDecs :: Proto -> [Arg RSession]
chanDecs p = p ^.. chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = prettyList . chanDecs

emptyProto :: Proto
emptyProto = MkProto Map.empty emptyConstraints []

chanPresent :: Proto -> Channel -> Bool
chanPresent p c = has (chans . at c . _Just) p

isEmptyProto :: Proto -> Bool
isEmptyProto p = p ^. chans . to Map.null

addChanOnly :: (Channel,RSession) -> Proto -> Proto
addChanOnly (c,s) = chans  %~ at c .~ Just s

data ConstraintFlag = WithConstraint | WithoutConstraints

addChanConstraint :: ConstraintFlag -> Channel -> Proto -> Proto
addChanConstraint WithoutConstraints _ = id
addChanConstraint WithConstraint     c = constraints %~ mapConstraints (c `Set.insert`)

addChan :: ConstraintFlag -> (Channel,RSession) -> Proto -> Proto
addChan flag (c,s) = addChanOnly (c,s) . addChanConstraint flag c

addChanWithOrder :: (Channel,RSession) -> Proto -> Proto
addChanWithOrder (c,s) p = p & addChan WithConstraint (c,s)
                             & orders %~ addOrder
  where addOrder []  = [[c]]
        addOrder css = map (c:) css

rmChanAndConstraint :: Channel -> Proto -> Proto
rmChanAndConstraint c p =
  p & chans . at c .~ Nothing
    & constraints %~ mapConstraints (c `Set.delete`)

rmChansAndConstraints :: [Channel] -> Proto -> Proto
rmChansAndConstraints = flip (foldr rmChanAndConstraint)

rmChan :: Channel -> Proto -> Proto
rmChan c p =
  p & rmChanAndConstraint c
    & orders . mapped %~ filter (/= c)

rmChans :: [Channel] -> Proto -> Proto
rmChans = flip (foldr rmChan)

substChans :: ConstraintFlag -> ([Channel], (Channel,RSession)) -> Proto -> Proto
substChans flag (cs, cs') p =
  p & orders . each %~ substList (l2s cs) (fst cs')
    & rmChansAndConstraints cs
    & addChan flag cs'

chanSession :: Channel -> Proto -> Maybe RSession
chanSession c p = p ^. chans . at c

chanSessions :: [Channel] -> Proto -> [Maybe RSession]
chanSessions cs p = map (`chanSession` p) cs

mkProto :: [(Channel,RSession)] -> Proto
mkProto css = MkProto (l2m css) (Constraints (l2s [l2s cs]))
                      (map return cs)
  where cs = map fst css

protoAx :: RSession -> Channel -> Channel -> [Channel] -> Proto
protoAx s c d es = mkProto ((c,s):(d,dual s):map (\e -> (e, log s)) es)

replProtoWhen :: (Channel -> Bool) -> Term -> Proto -> Proto
replProtoWhen cond n = chans . imapped %@~ replRSessionWhen where
  replRSessionWhen c s | cond c    = replRSession n s
                       | otherwise = s
-- -}
