{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Ling.Proto
  -- Types
  ( Proto
  -- Lenses
  , chans
  , orders
  , skel
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
import           Ling.Norm
import           Ling.Print
import           Ling.Proto.Skel      as Skel
import           Ling.Session
import           Ling.Utils

import           Control.Lens
import           Control.Monad.Except
import           Data.List            (sort)
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

data Proto = MkProto { _chans  :: Map Channel RSession
                     , _skel   :: Skel Channel
                     , _orders :: Orders
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
  if p ^. skel == ø then [] else
  " skeleton:"
  : map ("   " ++) (p^.skel.to pretty.to lines)
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
              (proto0^.skel        <> proto1^.skel)
              (proto0^.orders      <> proto1^.orders)
    | otherwise = error "mergeSession"

-- Not used
-- chanPresent :: Channel -> Getter Proto Bool
-- chanPresent c = chans . hasKey c

isEmptyProto :: Getter Proto Bool
isEmptyProto = chans . to Map.null

addChanOnly :: (Channel,RSession) -> Endom Proto
addChanOnly (c,s) = chans . at c .~ Just s

rmChanOnly :: Channel -> Endom Proto
rmChanOnly c p = p & chans . at c .~ Nothing

rmChansOnly :: [Channel] -> Endom Proto
rmChansOnly = composeMap rmChanOnly

-- TODO: integrate to the lens `order` as in `constraintSet`
cleanOrders :: Endom Proto
cleanOrders = orders . each %~ rmDups

rmChan :: Channel -> Endom Proto
rmChan c p =
  p & chans . at c .~ Nothing
    & orders . each . each %~ filter (/= c)
    & cleanOrders
    & skel %~ Skel.prune (l2s [c])

-- TODO can we use substChans as a generlized rmChan ?
-- TODO make rmChans first and rmChan derived from it.
rmChans :: [Channel] -> Endom Proto
rmChans = composeMap rmChan

substChans :: ([Channel], (Channel,RSession)) -> Endom Proto
{- This behavior is what reject:
  ten_par_par_seq = proc(c : [{},{}]) c[d,e] d{} e{}
   and also
  tensor2_tensor0_tensor0_sequence = proc(cd : [[], []]) cd[c,d] c[] d[]
substChans ([], (c,s)) p =
  p & addChanOnly (c,s)
    & skel %~ actS c
-}
substChans (cs, (c,s)) p =
  p & orders . each . each . each %~ substMember (scs, c)
    & cleanOrders
    & rmChansOnly cs
    & addChanOnly (c,s)
    & skel %~ Skel.prune scs
    where scs = l2s cs

chanSession :: Channel -> Lens' Proto (Maybe RSession)
chanSession c = chans . at c

chanSessions :: [Channel] -> Proto -> [Maybe RSession]
chanSessions cs p = [ p ^. chanSession c | c <- cs ]

mkProto :: [(Channel,RSession)] -> Proto
mkProto css = MkProto (l2m css)
                      (error "mkProto skel")
                      (error "mkProto order")

protoAx :: RSession -> [Channel] -> Proto
protoAx _ []             = mempty
protoAx s [c] | isSink s = mkProto [(c,s)]
protoAx s (c:d:es)       = mkProto ((c,s):(d,dual s):map (\e -> (e, log s)) es)
protoAx _ _              = error "protoAx: Not enough channels given to forward"

protoSendRecv :: [(Channel, Session -> Session)] -> Endom Proto
protoSendRecv cfs p =
  p & composeMap addChanOnly crs
    & skel %~ prllActS cs
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

checkConflictingChans :: MonadTC m => Proto -> Channel -> [Channel] -> m Proto
checkConflictingChans proto c cs =
  debugCheck (\res -> unlines $
     ["Checking channel conflicts for channels:"
     ,"  " ++ pretty cs
     ,"Input protocol:"
     ] ++ prettyProto proto ++
     ["Output protocol:"
     ] ++ prettyError prettyProto res) $
    (proto & skel %%~ checkSkel c cs)
    `catchError` (\_ ->
      throwError . unlines $
        ["These channels should be used independently:", pretty (sort cs)]
    )

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
