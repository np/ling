{-# LANGUAGE FlexibleInstances, TypeFamilies, MultiParamTypeClasses #-}
module Ling.Proc.Checker where

import Prelude hiding (log)
import Ling.Abs (Name)
import Ling.Utils
import Ling.Session
import Ling.Proto
import Ling.Norm
import Ling.Proc
import Ling.Constraint
import Ling.Term.Checker

import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.Reader (local, unless, when)
import Control.Monad.Error (throwError)
import Control.Lens

checkConflictingChans :: Proto -> [Channel] -> TC Proto
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

checkOrderedChans :: Proto -> [Channel] -> TC ()
checkOrderedChans proto cs =
  assert (or [ cs == sub os | os <- proto ^. orders ])
    ["These channels should be used in-order:", pretty cs]
  where
    sub = rmDups . filter (`Set.member` l2s cs)

checkEqSessions :: Name -> RSession -> Maybe RSession -> TC ()
checkEqSessions c s0 Nothing   = assertEqual s0 (one End) ["Unused channel: " ++ pretty c]
checkEqSessions c s0 (Just s1) =
  assertEqual s0 s1
    ["On channel " ++ pretty c ++ " sessions are not equivalent."
    ,"Given session (expanded):"
    ,"  " ++ pretty s0
    ,"Inferred session:"
    ,"  " ++ pretty s1
    ]

checkOptSession :: Name -> Maybe RSession -> Maybe RSession -> TC ()
checkOptSession _ Nothing   _   = return ()
checkOptSession c (Just s0) ms1 = checkRSession s0 >> checkEqSessions c s0 ms1

-- checkUnused c ms s: Check if the channel c is used given the
-- inferred session ms, and its dual ds.
checkUnused :: Name -> Maybe RSession -> RSession -> TC ()
checkUnused _ (Just _) _ = return ()
checkUnused c Nothing  s = assertEqual s (one End) ["Unused channel " ++ pretty c]

checkDual :: RSession -> RSession -> TC ()
checkDual (Repl s0 (Lit 1)) (Repl s1 (Lit 1)) =
  assertEqual s0 (dual s1)
    ["Sessions are not dual."
    ,"Given session (expanded):"
    ,"  " ++ pretty s0
    ,"Inferred dual session:"
    ,"  " ++ pretty s1
    ]
checkDual _ _ =
  throwError "Unexpected session replication in 'new'."

assertAbsent :: Channel -> Proto -> TC ()
assertAbsent c p =
  assert (p ^. chans . hasNoKey c)
    ["The channel " ++ pretty c ++ " has been re-used"]

isSendRecv :: Session -> Bool
isSendRecv (Snd _ s) = isSendRecv s
isSendRecv (Rcv _ s) = isSendRecv s
isSendRecv End       = True
isSendRecv _         = False

checkSlice :: (Channel -> Bool) -> (Channel, RSession) -> TC ()
checkSlice cond (c, rs) = when (cond c) $
  case rs of
    Repl s (Lit 1) ->
      assert (isSendRecv s) ["checkSlice: non send/recv session"]
    _ -> throwError "checkSlice: Replicated session"

checkProc :: Proc -> TC Proto
checkProc (prefs `Act` procs) = checkAct prefs procs

checkProcs :: [Proc] -> TC Proto
checkProcs [] = return emptyProto
checkProcs (proc : procs) = do
  proto0 <- checkProc  proc
  proto1 <- checkProcs procs
  v      <- view verbosity
  return $ parallelProtos v proto0 proto1

checkProgram :: Program -> TC ()
checkProgram (Program decs) = checkDecs decs

checkDecs :: [Dec] -> TC ()
checkDecs = foldr checkDec (return ())

checkDec :: Dec -> TC () -> TC ()
checkDec (Sig d typ mt)   kont = checkVarDef d typ mt kont
checkDec (Dat d cs)       kont = do
  checkNoDups ("in the definition of " ++ pretty d) cs
  checkNotIn evars "name" d
  mapM_ (checkNotIn ctyps "data constructor") cs
  local ((ctyps %~ Map.union (l2m [ (c,d) | c <- cs ]))
        .(evars . at d .~ Just TTyp)
        .(ddefs . at d .~ Just cs)) kont
checkDec (Dec d cds proc) kont = do
  checkNotIn pdefs "process" d
  let cs  = map _argName cds
  proto <- checkProc proc
  checkChanDecs proto cds
  let proto' = rmChans cs proto
  assert (proto' ^. isEmptyProto) $
    [ "These channels have not been introduced:"
    , prettyChanDecs proto']
  local (pdefs . at d .~ Just (ProcDef d cds proc proto)) kont

checkChanDec :: Proto -> ChanDec -> TC ()
checkChanDec proto (Arg c s) = checkOptSession c s $ proto ^. chanSession c

checkChanDecs :: Proto -> [ChanDec] -> TC ()
checkChanDecs = mapM_ . checkChanDec

debugCheckAct :: Proto -> Pref -> [Pref] -> Procs -> Endom (TC Proto)
debugCheckAct proto pref prefs procs m = do
  unless (null prefs && null procs) $
    debug $ [ "Checking " ++ actLabel pref ++ proc
            , "Inferred protocol for `" ++ proc' ++ "`:"
            ] ++ prettyProto proto
  proto' <- m
  debug $ ("Inferred protocol for" ++ proc ++ ":")
          : prettyProto proto'
  return proto'

  where proc  = " `" ++ pretty pref ++ " " ++ proc' ++ "`"
        proc' = pretty (actP prefs procs)

{-
Γ(P) is the protocol, namely mapping from channel to sessions of the process P
Δ(P) is the set of sequential channels, namely each set of C ∈ Δ(P) is a set
         of channels used in the same process, thus they cannot be in "tensor"
         with each other.
Union(Δ(P)) ≡ dom(Γ(P))

Ci={c0,...,cN}
∀ C ∈ Δ(P). ∃ ci. ci∈(C∩Ci)
∀ C,D ∈ Δ(P). C∩Ci ≡ D∩Ci ⇒ C ≡ D
    (OR: ∀ C,D ∈ Δ(P). C∩D∩Ci ≡ ø)
-------------------------------------------
Δ(c[c0,...,cN] P) = {C/Ci∪{c} | C ∈ Δ(P)}

or classically:
  Ci={c0,...,cN}
  ∀ C ∈ Δ(P). C∩Ci ≢ ø
  ∀ C,D ∈ Δ(P). C∩Ci # D∩Ci
  -------------------------------------------
  Δ(c[c0,...,cN] P) = {C/Ci∪{c} | C ∈ Δ(P)}

Γ()(c) = end
Γ(P | Q)(c) = Γ(P)(c) `or` Γ(Q)(c) where Γ(P)#Γ(Q)

Γ(send c t P)(c) = !T(t). Γ(P)(c)
Γ(send c t P)(d) = Γ(P)(d)

Γ(recv c (x : T) P)(c) = ?(x : T). Γ(P)(c)
Γ(recv c (x : T) P)(d) = Γ(P)(d)

Γ(new (c : S, d) P)(c) = end
Γ(new (c : S, d) P)(d) = end
Γ(new (c : S, d) P)(e) = Γ(P)(e)

Γ(c[c0,...,cN] P)(c) = [Γ(P)(c0),...,Γ(P)(cN)]
Γ(c[c0,...,cN] P)(d) = (Γ(P)/(c0,...,cN))(d)

Γ(c{c0,...,cN} P)(c) = {Γ(P)(c0),...,Γ(P)(cN)}
Γ(c{c0,...,cN} P)(d) = (Γ(P)/(c0,...,cN))(d)

-}
checkAct :: [Pref] -> Procs -> TC Proto
checkAct []             procs = checkProcs procs
checkAct (pref : prefs) procs = do
  proto <- checkVarDecs (actVarDecs pref) $ checkAct prefs procs
  debugCheckAct proto pref prefs procs $
    case pref of
      Nu (Arg c cOS) (Arg d dOS) -> do
        let ds = [c,d]
            [cSession,dSession] = chanSessions ds proto
            cNSession = defaultEndR cSession
            dNSession = defaultEndR dSession
        checkUnused c cSession dNSession
        checkUnused d dSession cNSession
        checkOptSession c cOS cSession
        checkOptSession d dOS dSession
        checkDual cNSession dNSession
        proto' <- checkConflictingChans proto ds
        return $ rmChans ds proto'
      Split k c dOSs -> do
        assertAbsent c proto
        let ds         = dOSs^..each.argName
            dsSessions = map defaultEndR $ chanSessions ds proto
            s          = array k dsSessions
        checkChanDecs proto dOSs
        (proto', flag) <-
          case k of
            TenK -> do
              proto' <- checkConflictingChans proto ds
              return (proto', WithoutConstraints)
            ParK ->
              return (proto,  WithConstraint)
            SeqK -> do
              checkOrderedChans proto ds
              return (proto,  WithConstraint)
        return $ substChans flag (ds, (c,one s)) proto'
      Send c e -> do
        let cSession = defaultEndR $ proto ^. chanSession c
        typ <- inferTerm' e
        return $ addChanWithOrder (c, mapR (Snd typ) cSession) proto
      Recv c (Arg _x typ) -> do
        checkTyp typ
        let cSession = defaultEndR $ proto ^. chanSession c
        return $ addChanWithOrder (c, mapR (Rcv typ) cSession) proto
      NewSlice cs t _i -> do
        checkTerm int t
        mapM_ (checkSlice (`notElem` cs)) (proto ^. chans . to m2l)
        return $ replProtoWhen (`elem` cs) t proto
      Ax s cs -> do
        v <- view verbosity
        -- TODO: we want to do here the same check as parallelProtos
        -- but with potentially different error message as they are not
        -- actually in parallel.
        return $ parallelProtos v proto (protoAx (one s) cs)
      At e cs -> do
        t <- inferTerm' e
        v <- view verbosity
        case t of
          TProto ss -> do
            assertEqual (length cs) (length ss)
               ["Expected " ++ show (length ss) ++ " channels, not " ++ show (length cs)]
            return $ parallelProtos v proto (mkProto $ zip cs ss)
          _ ->
            throwError . unlines $ ["Expected a protocol type, not:", pretty t]
