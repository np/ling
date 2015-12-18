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
  , assertUsed
  , assertAbsent
  , checkOrderedChans
  , checkSomeOrderChans
  , checkConflictingChans)
  where

import           Ling.Check.Base
import           Ling.Defs
import           Ling.Norm
import           Ling.Prelude
import           Ling.Print
import           Ling.Proto.Skel      (Skel, actS, prllActS, dotActS)
import qualified Ling.Proto.Skel      as Skel
import           Ling.Session
import           Ling.SubTerms

import qualified Data.Map             as Map
import qualified Data.Set             as Set
import           Prelude              hiding (log)

data Proto = MkProto { _chans  :: Map Channel RSession
                     , _skel   :: Skel Channel
                     }

$(makeLenses ''Proto)

prettyProto :: Proto -> [String]
prettyProto p = concat
  [[" channels:"]
  ,("   - " ++) <$> prettyChanDecs p
  ,if p ^. skel == ø then [] else
   " skeleton:"
   : p ^.. skel . prettied . indented 3]

-- toListOf chanDecs :: Proto -> [Arg Session]
chanDecs :: Fold Proto (Arg RSession)
chanDecs = chans . to m2l . each . to (uncurry Arg)

prettyChanDecs :: Proto -> [String]
prettyChanDecs = toListOf (chanDecs . prettied)

instance Monoid Proto where
  mempty = MkProto ø ø

  -- Use (<>) to combine protocols from processes which are composed in
  -- **parallel** (namely tensor).
  -- If the processes are in sequence use dotProto instead.
  mappend = combineProto TenK

instance PushDefs Proto where
  pushDefs = mkLet_ (chans . each . subTerms)

dotProto :: Op2 Proto
dotProto = combineProto SeqK

combineProto :: TraverseKind -> Op2 Proto
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
addChanOnly (c,s) = chans . at c ?~ s

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
pureProto c s = MkProto (l2m [(c,oneS s)]) (c `actS` ø)

mkProto :: TraverseKind -> [(Channel,Session)] -> Proto
mkProto k = arrayProto k . map (uncurry pureProto)

protoAx :: Session -> [Channel] -> Proto
protoAx _ []             = ø
protoAx s [c] | isSink s = pureProto c s
protoAx s (c:d:es)       = mkProto ParK ((c,s):(d,dual s):[(e, log s)|e <- es])
protoAx _ _              = error "protoAx: More channels should be given to forward or the session should a sink"

protoSendRecv :: [(Channel, Endom Session)] -> Endom Proto
protoSendRecv cfs p =
  p & composeMapOf each addChanOnly crs
    & skel %~ prllActS cs
  where crs = [ (c,mapR f (p ^. chanSession c . endedRS)) | (c,f) <- cfs ]
        cs = fst <$> cfs

-- Make sure the channel is used.
-- When the session is ended we want to skip this check and allow the
-- the channel to be unused.
assertUsed :: MonadError TCErr m => Proto -> Channel -> m ()
assertUsed proto c = assert (_Just `is` s) ["Unused channel " ++ pretty c]
  where s = proto ^. chanSession c

assertAbsent :: MonadError TCErr m => Proto -> Channel -> m ()
assertAbsent proto c =
  assert (proto ^. chans . hasNoKey c)
    ["The channel " ++ pretty c ++ " has been re-used"]

checkConflictingChans :: MonadTC m => Proto -> Maybe Channel -> [Channel] -> m Proto
checkConflictingChans proto c cs =
  debugCheck (\res -> unlines $
    ["Checking channel conflicts for channels:"
    ,"  " ++ pretty cs ++ " to be replaced by " ++ pretty c
    ,"Input protocol:"
    ] ++ prettyProto proto ++
    ["Output protocol:"
    ] ++ prettyError prettyProto res) $
    (proto & skel %%~ Skel.check c cs)
    `catchError` (\err -> do
      debug err
      throwError . unlines $
        ["These channels should be used independently:", pretty (Comma (sort cs))]
    )

checkOrderedChans :: MonadTC m => Proto -> [Channel] -> m ()
checkOrderedChans proto cs = do
  debug . unlines $
    ["Checking channel ordering for:"
    ,"  " ++ pretty cs
    ,"Protocol:"
    ] ++ prettyProto proto ++
    ["Selected ordering:"
    ] ++ (my ^.. prettied . indented 2)
  assert (ref == my)
    ["These channels should be used in-order:", pretty (Comma cs)]
    where ref = cs `dotActS` ø
          my  = Skel.select (l2s cs) (proto^.skel)

checkSomeOrderChans :: MonadTC m => Proto -> Set Channel -> m ()
checkSomeOrderChans proto cs = do
  b <- view $ tcOpts.strictPar
  debug . unlines $
    ["Checking SOME channel ordering for:"
    ,"  " ++ pretty cs
    ,"Protocol:"
    ] ++ prettyProto proto ++
    ["Selected ordering:"
    ,"  " ++ pretty my]
  assert (not b || Just cs == my)
    ["These channels should be used in some order (not in parallel):", pretty (s2l cs)]
    where my = Skel.dotChannelSet $ Skel.select cs (proto^.skel)

replProtoWhen :: (Channel -> Bool) -> RFactor -> Endom Proto
replProtoWhen cond n = chans . imapped %@~ replRSessionWhen where
  replRSessionWhen c s | cond c    = replRSession n s
                       | otherwise = s
-- -}
