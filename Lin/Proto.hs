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
  : map ("  " ++) (map show (p ^. orders))

chanDecs :: Proto -> [Arg Session]
chanDecs p = p ^.. chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = prettyList . chanDecs

emptyProto :: Proto
emptyProto = MkProto Map.empty emptyConstraints []

addChanOnly :: Proto -> (Channel,Session) -> Proto
addChanOnly p (c,s) = p & chans  %~ at c .~ Just s
                        & orders %~ ([]:)
                        & orders . mapped %~ (c:)

addChan :: Proto -> (Channel,Session) -> Proto
addChan p (c,s) = addChanOnly p (c,s)
                & constraints %~ mapConstraints (c `Set.insert`)

chanPresent :: Proto -> Channel -> Bool
chanPresent p c = has (chans . at c . _Just) p

isEmptyProto :: Proto -> Bool
isEmptyProto p = p ^. chans . to Map.null

rmChan :: Channel -> Proto -> Proto
rmChan c p = p & chans . at c .~ Nothing
               & constraints %~ mapConstraints (c `Set.delete`)
               & orders . mapped %~ filter (/= c)

rmChans :: Proto -> [Channel] -> Proto
rmChans = foldr rmChan

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
replProto n p = p & chans . mapped %~ replSessionTerm n
