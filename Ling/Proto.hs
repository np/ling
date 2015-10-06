{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Ling.Proto
  -- Types
  ( Proto
  , ConstraintFlag (WithConstraint, WithoutConstraints)
  -- Lenses
  , chans
  , constraints
  , orders
  -- Operations
  , prettyProto
  , prettyChanDecs
  , isEmptyProto
  , rmChan
  , rmChans
  , substChans
  , chanSession
  , chanSessions
  , mkProto
  , protoAx
  , protoSendRecv
  , replProtoWhen
  , orderedChans
  , assertAbsent
  , checkOrderedChans
  , checkConflictingChans)
  where

import           Ling.Check.Base
import           Ling.Constraint
import           Ling.Norm
import           Ling.Print
import           Ling.Session
import           Ling.Utils

import           Control.Lens
import           Control.Monad.Except
import           Data.Map             (Map, keysSet)
import qualified Data.Map             as Map
import           Data.Set             (intersection, member)
import qualified Data.Set             as Set
import           Prelude              hiding (log)

-- ^ first layer:  parallel processes
--   second layer: order implied by `.`
--   third layer:  parallel prefixes
-- Example:
-- [[[a],[b],[c,d],[e]],[[x],[y,z]]]
-- should be read as:
-- ((a.b.(c | d).e) | (x.(y | z)))
type Orders = [[[Channel]]]

data Proto = MkProto { _chans       :: Map Channel RSession
                     , _constraints :: Constraints
                     , _orders      :: Orders
                     }

$(makeLenses ''Proto)

prettyOrders :: [[[Channel]]] -> [String]
prettyOrders = map $ pretty . Order . map Prll

prettyProto :: Proto -> [String]
prettyProto p =
  [" channels:"]
  ++
  map ("   - " ++) (prettyChanDecs p)
  ++
  if p ^. constraints . to noConstraints then [] else
  " constraints:"
  : map ("   - " ++) (p^.constraints.to prettyConstraints)
  ++
  if p ^. orders . to null then [] else
  " orders:"
  : map ("   - " ++) (p^.orders.to prettyOrders)

-- toListOf chanDecs :: Proto -> [Arg Session]
chanDecs :: Fold Proto (Arg RSession)
chanDecs = chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = toListOf (chanDecs . to pretty)

instance Monoid Proto where
  mempty = MkProto ø ø ø
  mappend proto0 proto1
    | Set.null (keysSet (proto0^.chans) `intersection` keysSet (proto1^.chans)) =
      MkProto (proto0^.chans       <> proto1^.chans)
              (proto0^.constraints <> proto1^.constraints)
              (proto0^.orders      <> proto1^.orders)
    | otherwise = error "mergeSession"

-- Not used
-- chanPresent :: Channel -> Getter Proto Bool
-- chanPresent c = chans . hasKey c

isEmptyProto :: Getter Proto Bool
isEmptyProto = chans . to Map.null

addChanOnly :: (Channel,RSession) -> Endom Proto
addChanOnly (c,s) = chans . at c .~ Just s

data ConstraintFlag = WithConstraint | WithoutConstraints

addChanConstraint :: ConstraintFlag -> Channel -> Endom Proto
addChanConstraint WithoutConstraints _ = id
addChanConstraint WithConstraint     c = constraints %~ constrainChan c

--addChan :: ConstraintFlag -> (Channel,RSession) -> Endom Proto
--addChan flag (c,s) = addChanOnly (c,s) . addChanConstraint flag c

rmChanAndConstraint :: Channel -> Endom Proto
rmChanAndConstraint c p =
  p & chans . at c .~ Nothing
    & constraints %~ unconstrainChan c

rmChansAndConstraints :: [Channel] -> Endom Proto
rmChansAndConstraints = composeMap rmChanAndConstraint

-- TODO: integrate to the lens `order` as in `constraintSet`
cleanOrders :: Endom Proto
cleanOrders = orders . each %~ rmDups

rmChan :: Channel -> Endom Proto
rmChan c p =
  p & rmChanAndConstraint c
    & orders . each . each %~ filter (/= c)
    & cleanOrders

-- TODO can we use substChans as a generlized rmChan ?
-- TODO make rmChans first and rmChan derived from it.
rmChans :: [Channel] -> Endom Proto
rmChans = composeMap rmChan

substChans :: ConstraintFlag -> ([Channel], (Channel,RSession)) -> Endom Proto
substChans flag (cs, (c,s)) p =
  p & orders . each . each . each %~ substMember (scs, c)
    & cleanOrders
    & rmChansAndConstraints cs
    & addChanOnly (c,s)
    & addChanConstraint flag c
    where scs = l2s cs

chanSession :: Channel -> Lens' Proto (Maybe RSession)
chanSession c = chans . at c

chanSessions :: [Channel] -> Proto -> [Maybe RSession]
chanSessions cs p = [ p ^. chanSession c | c <- cs ]

mkProto :: [(Channel,RSession)] -> Proto
mkProto css = MkProto (l2m css) (singleConstraint (l2s cs))
                      (error "mkProto order")
  where cs = map fst css

protoAx :: RSession -> [Channel] -> Proto
protoAx _ []             = mempty
protoAx s [c] | isSink s = mkProto [(c,s)]
protoAx s (c:d:es)       = mkProto ((c,s):(d,dual s):map (\e -> (e, log s)) es)
protoAx _ _              = error "protoAx: Not enough channels given to forward"

protoSendRecv :: [(Channel, Session -> Session)] -> Endom Proto
protoSendRecv cfs p =
  p & composeMap addChanOnly crs
    & constraints %~ constrainPrllChans cs
    & orders %~ addOrder
    & cleanOrders
  where addOrder []  = [[cs]]
        addOrder css = map (cs:) css
        crs = [ (c,mapR f (defaultEndR $ p ^. chanSession c)) | (c,f) <- cfs ]
        cs = map fst cfs

assertAbsent :: MonadError TCErr m => Channel -> Proto -> m ()
assertAbsent c p =
  assert (p ^. chans . hasNoKey c)
    ["The channel " ++ pretty c ++ " has been re-used"]

checkConflictingChans :: MonadTC m => Proto -> [Channel] -> m Proto
checkConflictingChans proto cs =
   mapM_ check iss >>
   return (proto & constraints . constraintSet .~ Set.insert com1 mix)
  where
    scs = l2s cs
    iss = map (Set.intersection scs) (s2l ss)
    ss  = proto ^. constraints . constraintSet
    (mix, com) = Set.partition (Set.null . Set.intersection scs) ss
    com1 = Set.unions (s2l com)
    check cc = assert (Set.size cc < 2)
      ["These channels should be used independently:", pretty (s2l cc)]

orderedChans :: Proto -> [Channel] -> Bool
orderedChans proto cs =
  or [ cs == sub os | os <- proto ^. orders ]
  where
    sub = rmDups . sing . (map . filter) (`member` l2s cs)
    sing xs = [ x | [x] <- xs ]

checkOrderedChans :: MonadError TCErr m => Proto -> [Channel] -> m ()
checkOrderedChans proto cs =
  assert (orderedChans proto cs)
    ["These channels should be used in-order:", pretty cs]

replProtoWhen :: (Channel -> Bool) -> Term -> Endom Proto
replProtoWhen cond n = chans . imapped %@~ replRSessionWhen where
  replRSessionWhen c s | cond c    = replRSession n s
                       | otherwise = s
-- -}
