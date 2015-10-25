{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
module Ling.Proto
  -- Types
  ( Proto
  -- Lenses
  , chans
  , skel
  -- Operations
  , dotProto
  , prettyProto
  , prettyChanDecs
  , isEmptyProto
  , rmChans
  , substChans
  , chanSession
  , chanSessions
  , arrayProto
  , pureProto
  , mkProto
  , protoAx
  , protoSendRecv
  , replProtoWhen
  , assertAbsent
  , checkOrderedChans
  , checkSomeOrderChans
  , checkConflictingChans)
  where

import           Ling.Check.Base
import           Ling.Norm
import           Ling.Print
import           Ling.Proto.Skel      (Skel, actS, prllActS, dotActS)
import qualified Ling.Proto.Skel      as Skel
import           Ling.Session
import           Ling.Utils

import           Control.Lens
import           Control.Monad.Except
import           Data.List            (sort)
import           Data.Map             (Map, keysSet)
import qualified Data.Map             as Map
import           Data.Set             (Set)
import qualified Data.Set             as Set
import           Prelude              hiding (log)

data Proto = MkProto { _chans  :: Map Channel RSession
                     , _skel   :: Skel Channel
                     }

$(makeLenses ''Proto)

prettyProto :: Proto -> [String]
prettyProto p =
  [" channels:"]
  ++
  map ("   - " ++) (prettyChanDecs p)
  ++
  if p ^. skel == ø then [] else
  " skeleton:"
  : map ("   " ++) (p^.skel.to pretty.to lines)

-- toListOf chanDecs :: Proto -> [Arg Session]
chanDecs :: Fold Proto (Arg RSession)
chanDecs = chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = toListOf (chanDecs . to pretty)

instance Monoid Proto where
  mempty = MkProto ø ø

  -- Use (<>) to combine protocols from processes which are composed in
  -- **parallel** (namely tensor).
  -- If the processes are in sequence use dotProto instead.
  mappend = combineProto TenK

dotProto :: Proto -> Proto -> Proto
dotProto = combineProto SeqK

combineProto :: TraverseKind -> Proto -> Proto -> Proto
combineProto k proto0 proto1 =
  if Set.null common then
    MkProto (proto0^.chans <> proto1^.chans)
            (Skel.combineS k (proto0^.skel) (proto1^.skel))
  else
    error . unlines $ ["These channels are re-used:", pretty common]
  where
    common = keysSet (proto0^.chans) `Set.intersection` keysSet (proto1^.chans)

arrayProto :: TraverseKind -> [Proto] -> Proto
arrayProto k = foldr (combineProto k) ø

-- Not used
-- chanPresent :: Channel -> Getter Proto Bool
-- chanPresent c = chans . hasKey c

isEmptyProto :: Getter Proto Bool
isEmptyProto = chans . to Map.null

addChanOnly :: (Channel,RSession) -> Endom Proto
addChanOnly (c,s) = chans . at c .~ Just s

rmChansOnly :: [Channel] -> Endom Proto
rmChansOnly cs = chans %~ deleteList cs

rmChans :: [Channel] -> Endom Proto
rmChans cs p =
  p & rmChansOnly cs
    & skel %~ Skel.prune (l2s cs)

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
  p & rmChansOnly cs
    & addChanOnly (c,s)
    & skel %~ Skel.subst (substMember (l2s cs, Skel.Act c) Skel.Act)

chanSession :: Channel -> Lens' Proto (Maybe RSession)
chanSession c = chans . at c

chanSessions :: [Channel] -> Proto -> [Maybe RSession]
chanSessions cs p = [ p ^. chanSession c | c <- cs ]

pureProto :: Channel -> Session -> Proto
pureProto c s = MkProto (l2m [(c,one s)]) (c `actS` ø)

mkProto :: TraverseKind -> [(Channel,Session)] -> Proto
mkProto k = arrayProto k . map (uncurry pureProto)

protoAx :: Session -> [Channel] -> Proto
protoAx _ []             = mempty
protoAx s [c] | isSink s = pureProto c s
protoAx s (c:d:es)       = mkProto ParK ((c,s):(d,dual s):map (\e -> (e, log s)) es)
protoAx _ _              = error "protoAx: Not enough channels given to forward"

protoSendRecv :: [(Channel, Session -> Session)] -> Endom Proto
protoSendRecv cfs p =
  p & composeMap addChanOnly crs
    & skel %~ prllActS cs
  where crs = [ (c,mapR f (defaultEndR $ p ^. chanSession c)) | (c,f) <- cfs ]
        cs = map fst cfs

assertAbsent :: MonadError TCErr m => Channel -> Proto -> m ()
assertAbsent c p =
  assert (p ^. chans . hasNoKey c)
    ["The channel " ++ pretty c ++ " has been re-used"]

checkConflictingChans :: MonadTC m => Proto -> Maybe Channel -> [Channel] -> m Proto
checkConflictingChans proto c cs =
  debugCheck (\res -> unlines $
    ["Checking channel conflicts for channels:"
    ,"  " ++ pretty cs
    ,"Input protocol:"
    ] ++ prettyProto proto ++
    ["Output protocol:"
    ] ++ prettyError prettyProto res) $
    (proto & skel %%~ Skel.check c cs)
    `catchError` (\_err ->
      throwError . unlines $
        ["These channels should be used independently:", pretty (sort cs)]
        -- ++ [_err]
    )

checkOrderedChans :: MonadTC m => Proto -> [Channel] -> m ()
checkOrderedChans proto cs = do
  debug . unlines $
    ["Checking channel ordering for:"
    ,"  " ++ pretty cs
    ,"Protocol:"
    ] ++ prettyProto proto ++
    ["Selected ordering:"
    ] ++ (map ("  "++) . lines . pretty $ my)
  assert (ref == my)
    ["These channels should be used in-order:", pretty cs]
    where ref = cs `dotActS` ø
          my  = Skel.select (l2s cs) (proto^.skel)

replProtoWhen :: (Channel -> Bool) -> Term -> Endom Proto
replProtoWhen cond n = chans . imapped %@~ replRSessionWhen where
  replRSessionWhen c s | cond c    = replRSession n s
                       | otherwise = s
-- -}
