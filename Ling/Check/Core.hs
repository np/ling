{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
module Ling.Check.Core where

import           Ling.Check.Base
import           Ling.Defs
import           Ling.Norm
import           Ling.Print
import           Ling.Proc
import           Ling.Proto
import           Ling.Reduce
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst           (substScoped)
import           Ling.Prelude         hiding (subst1)
import           Prelude              hiding (log)

-- The protocol is the result of inferrence.
-- The channel has a potential session annotation.
checkChanDec :: Proto -> ChanDec -> TC RSession
checkChanDec proto (ChanDec c r ms0) = do
  errorScope c $ do
    checkRFactor r
    checkEquivalence "Replication factors are not equivalent."
                     "Annotation:" (pure r)
                     "Inferred:"   (pure (ms1 ^. endedRS . rfactor))
  case ms0 of
    Nothing -> return ()
    Just s0 ->
      case ms1 of
        Nothing -> assert (endRS `is` s0) ["Unused channel " ++ pretty c]
        Just s1 -> errorScope c (checkRSession s0) >> checkEqSessions c (pure s0) (pure s1)
  return $ ms1 ^. endedRS

  where ms1 = proto ^. chanSession c

checkProc :: Proc -> TC Proto
checkProc proc0 =
  debugCheck (\proto -> unlines $
              [ "Checking proc `" ++ pretty proc0 ++ "`"
              , "Inferred protocol for the whole process:"
              ] ++ prettyError prettyProto proto) $
  case proc0 of
    Procs procs -> checkProcs procs

    Replicate k r i proc1 -> do
      checkRFactor r
      proto <- local (scopeVarDef i intTyp Nothing) $
                 checkProc proc1
      pure $ replProto k r proto

    LetP defs proc1 ->
       mkLet__ . Scoped ø defs <$> checkDefs defs (checkProc proc1)

    _ | Just (pref@(Prll acts), proc1) <- proc0 ^? _PrefDotProc -> do
      checkPrefWellFormness pref
      checkPref pref =<< checkVarDecs (actVarDecs =<< acts) (checkProc proc1)

    proc1 `Dot` proc2 -> dotProto <$> checkProc proc1 <*> checkProc proc2

    _ -> error $ "checkProc: IMPOSSIBLE " ++ show proc0

sendRecvSession :: Act -> TC (Channel, EndoM TC Session)
sendRecvSession = \case
  Send c os e ->
    -- See for the use of this type annotation: https://github.com/np/ling/issues/13
    case os of
      Nothing -> (,) c . (pure .) . sendS <$> inferTerm e
      Just s0  -> do
        checkSession s0
        s1 <- tcReduce s0
        case s1 ^. scoped of
          IO Write (Arg x typ) s2 ->
            checkCheckedAnnTerm (Ann (mkLetS . (s1 $>) <$> typ) e) $>
              (c, \s -> checkEqSessions c (pure s) (s1 *> subst1 (x, Ann typ e) s2) $> s0)
            -- Instead of returning s0 we could return `mkLetS s1`
          _ ->
            tcError . unlines $
              ["Annotation when sending on channel " <> pretty c <> " should be of the form `!(_ : _). _`."
              ,"Instead the current annotation:"
              ,"  " <> pretty s0
              ,"which reduces to: "
              ,"  " <> pretty (substScoped s1)]
  Recv c arg@(Arg _c typ) ->
    checkMaybeTyp typ $> (c, (pure .) $ depRecv arg)
  _ -> tcError "typeSendRecv: Not Send/Recv"

checkPref :: Pref -> Proto -> TC Proto
checkPref (Prll pref) proto
  | null pref =
      return proto
  | all isSendRecv pref = do
      css <- mapM sendRecvSession pref
      proto' <- protoSendRecv css proto
      forM_ css $ \(c, _)-> assertRepl1 proto c
      when (length pref >= 1) $
        debug . unlines $
          [ "Checked parallel prefix: `" ++ pretty pref ++ "`"
          , "Inferred protocol for the sub-process:"
          ] ++ prettyProto proto ++
          [ "Inferred protocol for the whole process:"
          ] ++ prettyProto proto'
      return proto'
  | [act] <- pref =
      checkAct act proto
  | otherwise =
      tcError $ "Unsupported parallel prefix " ++ pretty pref

checkProcs :: Procs -> TC Proto
checkProcs (Prll procs) = mconcat <$> traverse checkProc procs

checkRFactor :: RFactor -> TC ()
checkRFactor (RFactor t) = checkTerm intTyp t

checkAx :: Session -> [Channel] -> TC Proto
checkAx s cs = do
  checkSession s
  case cs of
    [] ->
      pure ø
    [c] -> do
      b <- isSink s
      if b then pure (pureProto c s)
           else tcError . concat $
                  ["Cannot forward only channel ", pretty c, " with session ", pretty s, ".\n"
                  ,"More channels should be given to forward or the session should a sink."]
    c:d:es ->
      pure $ mkProto ParK ((c,s):(d,dual s):[(e, log s)|e <- es])

-- _SingleSendSession :: Prism

checkNewPatt :: AllocAnnots -> Proto -> CPatt -> TC Proto
checkNewPatt anns proto = \case
  ChanP (ChanDec c r s0) -> do
    let s = proto ^. chanSession c . endedRS
    unless (endRS `is` s) $ assertUsed proto c
    checkOneR r
    s1 <- checkOneS (s0 ^. endedRS)
    case s1 of
      IO Write (Arg x mty) (Array SeqK (Sessions [])) | x == anonName -> do
        checkNewChan anns c s mty $> rmChans [c] proto
      _ ->
        tcError "Unexpected channel allocation"
  ArrayP k pats | Just cds <- pats ^? _Chans -> do
    let cs = cds ^.. each . cdChan
        crs = [ (c, proto ^. chanSession c . endedRS) | ChanDec c _ _ <- cds ]
        csNSession = crs ^.. each . _2
    unless (all (is endRS) csNSession) $
      for_ cs $ assertUsed proto
    for_ cds $ checkChanDec proto
    proto' <-
      case k of
        TenK -> do
          checkDual csNSession
          checkConflictingChans proto Nothing cs
        SeqK -> do
          checkSeqNew anns crs
          checkOrderedChans proto cs $> proto
        ParK -> error "checkAct: IMPOSSIBLE"
    -- This rmChans is potentially partly redundant.
    -- We might `assert` that `cs` is no longer in the `skel`
    return $ rmChans cs proto'
  _ -> tcError "Unexpected channel allocation"


{-
WARNING this comment is outdated.
In particular the use of skeletons is important.

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

Γ(c <- t. P)(c) = !T(t). Γ(P)(c)
Γ(c <- t. P)(d) = Γ(P)(d)

Γ(let (x : T) <- P)(c) = ?(x : T). Γ(P)(c)
Γ(let (x : T) <- P)(d) = Γ(P)(d)

Γ(new [c : S, d] P)(c) = end
Γ(new [c : S, d] P)(d) = end
Γ(new [c : S, d] P)(e) = Γ(P)(e)

Γ(c[c0,...,cN] P)(c) = [Γ(P)(c0),...,Γ(P)(cN)]
Γ(c[c0,...,cN] P)(d) = (Γ(P)/(c0,...,cN))(d)

Γ(c{c0,...,cN} P)(c) = {Γ(P)(c0),...,Γ(P)(cN)}
Γ(c{c0,...,cN} P)(d) = (Γ(P)/(c0,...,cN))(d)

-}
checkAct :: Act -> Proto -> TC Proto
checkAct act proto =
  debugCheck (\proto' -> unlines $
              [ "Checking act `" ++ pretty act ++ "`"
              , "Inferred protocol for the sub-process:"
              ] ++ prettyProto proto ++
              [ "Inferred protocol for the whole process:"
              ] ++ prettyError prettyProto proto') $
  case act of
    Nu anns pat -> do
      for_ anns $ checkTerm allocationTyp
      checkNewPatt anns proto pat
    Split c pat ->
      case pat ^? _ArrayCs of
        Just (k, dOSs) -> do
          assertAbsent proto c
          for_ dOSs $ checkChanDec proto
          let ds         = dOSs ^.. each . cdChan
              dsSessions = ds & each %~ \d -> proto ^. chanSession d . endedRS
              s          = array k dsSessions
          proto' <-
            case k of
              TenK -> checkConflictingChans proto (Just c) ds
              ParK -> checkSomeOrderChans proto (l2s ds) $> proto
              SeqK -> checkOrderedChans proto ds $> proto
          return $ substChans (ds, (c,oneS s)) proto'
        Nothing ->
          error "Check.Core: unsupported split"
    Send{} -> error "IMPOSSIBLE: use checkPref instead"
    Recv{} -> error "IMPOSSIBLE: use checkPref instead"
    Ax s cs -> do
      proto' <- checkAx s cs
      return $ proto' `dotProto` proto
    At e p -> do
      sc <- tcScope ()
      ss <- unTProto . (sc $>) =<< inferTerm e
      proto' <- checkCPatt (sc *> (wrapSessions <$> ss)) p
      return $ proto' `dotProto` proto

unTProto :: Scoped Term -> TC (Scoped Sessions)
unTProto st0 = do
  let st1 = reduce st0 ^. reduced
  case st1 ^. scoped of
    TProto ss  -> pure (st1 $> ss)
    Case u brs -> mkCaseSessions substScoped (==) u <$> branches (unTProto . (st0 $>)) brs
    -- ^ avoiding this call to substScoped would be nice
  {-
    Case u brs -> do env <- tcEqEnv
                    mkCaseSessions (equiv env) u <$> branches unTProto brs
  -}
    t1         -> tcError . unlines $ ["Expected a protocol type, not:", pretty t1]

checkCPatt :: Scoped Session -> CPatt -> TC Proto
checkCPatt s = \case
  ChanP cd ->
    let proto = pureProto (cd ^. cdChan) (substScoped s) in
    -- ^ avoiding this call to substScoped would be nice
    checkChanDec proto cd $> proto
  ArrayP kpat pats ->
    let rs = reduce s ^. reduced in
    case rs ^. scoped of
      Array k (Sessions ss) -> do
        assert (kpat == k)
          ["Expected an array splitting pattern with " ++ kindSymbols kpat ++
           " not " ++ kindSymbols k]
        assert (length pats == length ss)
          ["Expected " ++ show (length ss) ++ " sub-patterns, not " ++
            show (length pats)]
        arrayProto k <$> zipWithM checkCPattR (map (rs *> s $>) ss) pats
      _ ->
        tcError $ "Unexpected array splitting pattern (" ++
                  kindSymbols kpat ++ ") for session " ++ pretty (substScoped s)

checkCPattR :: Scoped RSession -> CPatt -> TC Proto
checkCPattR ss pat
  | Just s <- ss ^? scoped . _OneS = checkCPatt (ss $> s) pat
  | otherwise = tcError "Unexpected pattern for replicated session"

inferBranch :: (name, Term) -> TC (name, Typ)
inferBranch (n,t) = (,) n <$> inferTerm t

inferTerm :: Term -> TC Typ
inferTerm e0 = debug ("Inferring type of " ++ pretty e0) >> case e0 of
  Let defs t   -> mkLet defs <$> checkDefs defs (inferTerm t)
  Lit l        -> pure $ literalType l
  TTyp         -> pure TTyp -- type-in-type
  Def k d es   -> inferDef k d es
  Lam arg t    -> TFun arg <$> checkVarDec arg (inferTerm t)
  Con n        -> conType n
  Case t brs   -> join $ caseType t <$> inferTerm t <*> list inferBranch brs
  Proc cs proc -> inferProcTyp cs proc
  TFun arg s   -> checkVarDec arg (checkTyp s) $> TTyp
  TSig arg s   -> checkVarDec arg (checkTyp s) $> TTyp
  TProto ss    -> for_ (ss ^. _Sessions) checkRSession $> TTyp
  TSession s   -> checkSession s               $> sessionTyp

inferProcTyp :: [ChanDec] -> Proc -> TC Typ
inferProcTyp cds proc = do
  let cs  = cds ^.. each . cdChan
  proto <- checkProc proc
  rs <- forM cds $ checkChanDec proto
  let proto' = rmChans cs proto
  assert (proto' ^. isEmptyProto) $
    "These channels have not been introduced:" :
    prettyChanDecs proto'
  return $ tProto rs

checkTyp :: Typ -> TC ()
checkTyp = checkTerm TTyp

checkMaybeTyp :: Maybe Typ -> TC ()
checkMaybeTyp = checkMaybeTerm TTyp

checkTerm :: Typ -> Term -> TC ()
checkTerm expectedTyp e = do
  inferredTyp <- inferTerm e
  debug . unlines $
    ["Checking term"
    ,"exp:      " ++ pretty e
    ,"expected: " ++ pretty expectedTyp
    ,"inferred: " ++ pretty inferredTyp
    ]
  checkTypeEquivalence expectedTyp inferredTyp

checkMaybeTerm :: Typ -> Maybe Term -> TC ()
checkMaybeTerm _   Nothing   = return ()
checkMaybeTerm typ (Just tm) = checkTerm typ tm

-- Like `checkAnnTerm` but the type annotation is already checked.
checkCheckedAnnTerm :: AnnTerm -> TC Typ
checkCheckedAnnTerm (Ann Nothing    tm) = inferTerm tm
checkCheckedAnnTerm (Ann (Just typ) tm) = checkTerm typ tm $> typ

checkAnnTerm :: AnnTerm -> TC Typ
checkAnnTerm (Ann Nothing    tm) = inferTerm tm
checkAnnTerm (Ann (Just typ) tm) = checkTyp typ >> checkTerm typ tm $> typ

inferDef :: DefKind -> Name -> [Term] -> TC Typ
inferDef _ f es = do
  mtyp <- view $ evars . at f
  case mtyp of
    Just typ -> tcScope typ >>= \styp -> checkApp f 0 styp es
    Nothing  -> tcError $ "unknown definition " ++ pretty f ++
                          if f == anonName then
                            "\n\nHint: While `_` is allowed as a name for a definition, one cannot reference it."
                          else
                            ""


-- `checkApp f n typ es`
-- `f`   is the name of the definition currently checked
-- `n`   number of already checked arguments
-- `typ` the type of definition (minus the previously checked arguments)
-- `es`  the list of arguments
checkApp :: Name -> Int -> Scoped Typ -> [Term] -> TC Typ
checkApp _ _ ty0 []     = return $ mkLetS ty0
checkApp f n ty0 (e:es) =
  let ty1 = reduce ty0 ^. reduced in
  case ty1 ^. scoped of
    TFun (Arg x mty) s -> do
      debug . unlines $
        ["Check application:"
        ,"f:   " ++ pretty f
        ,"ty0: " ++ pretty ty0
        ,"ty1: " ++ pretty ty1
        ,"e:   " ++ pretty e
        ,"es:  " ++ pretty es
        {-
        ,"x:    " ++ pretty x
        ,"ty:   " ++ pretty ty
        ,"s:    " ++ pretty s
        -}
        ]
      ty <- requireAnnotation "argument" x mty
      errorScope' (concat ["While applying argument number ", show (n + 1), " of `", pretty f, "`"]) $
        checkTerm (mkLetS (ty0 *> ty1 $> ty)) e
      checkApp f (n + 1) (ty0 *> ty1 *> subst1 (x, Ann (Just ty) e) s) es
    _ -> tcError ("Too many arguments given to " ++ pretty f ++ ", " ++
                     show n ++ " arguments expected and " ++
                     show (n + 1 + length es) ++ " were given.")

checkOneS :: RSession -> TC Session
checkOneS (s `Repl` r) = checkOneR r >> checkSession s $> s

checkRSession :: RSession -> TC ()
checkRSession (s `Repl` r) = checkSession s >> checkRFactor r

checkSession :: Session -> TC ()
checkSession s0 = case s0 of
  TermS _ t   -> checkTerm sessionTyp t
  IO _ arg s  -> checkVarDec arg $ checkSession s
  Array _ ss  -> for_ (ss ^. _Sessions) checkRSession

{- Not used yet...
   This makes sense to use these when the definitions should scope on everything which is
   being type checked. Otherwise prefer the use of Scoped, or mkLet.

localDefs :: Defs -> Endom (TC b)
localDefs defs = local $ edefs <>~ defs

localScope :: Scoped a -> Endom (TC b)
localScope = localDefs . view ldefs
-}

-- The arguments are assumed to be already checked,
-- otherwise use `checkDef` or `checkVarDec`.
scopeVarDef :: Name -> Typ -> Maybe Term -> Endom TCEnv
scopeVarDef x typ mtm
  | x == anonName = id
  | otherwise     =
      (evars . at x ?~ typ)
    . (edefs . at x .~ (Ann (Just typ) <$> mtm))

checkArg :: Arg (Ann (TC Typ) (Maybe Term)) -> Endom (TC a)
checkArg (Arg x (Ann tc mtm)) kont = do
  checkNotIn evars "name" x
  ty <- errorScope x tc
  local (scopeVarDef x ty mtm) kont

checkDef :: Arg AnnTerm -> Endom (TC a)
checkDef (Arg x ann@(Ann _ tm)) = checkArg (Arg x (Ann tc (Just tm))) where
  tc = case ann of
        Ann (Just ty) (Def Undefined x' [])
          | x == x' -> checkTyp ty $> ty
        _           -> checkAnnTerm ann

-- Note that this is up to you to make the definitions in scope of the
-- result if necessary.
checkDefs :: Defs -> Endom (TC a)
checkDefs = composeMapOf each checkDef

checkVarDec :: VarDec -> Endom (TC a)
checkVarDec (Arg x mty) = checkArg (Arg x (Ann tc Nothing)) where
  tc = case mty of
        Nothing -> tcError "Missing type signature"
        Just ty -> checkTyp ty $> ty

-- Check a "telescope", where bindings scope over the following ones
checkVarDecs :: [VarDec] -> Endom (TC a)
checkVarDecs = composeMapOf each checkVarDec
