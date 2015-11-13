{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Ling.Check.Core where

import           Ling.Check.Base
import           Ling.Norm
import           Ling.Print
import           Ling.Proto
import           Ling.Reduce
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst           (unScoped)
import           Ling.Prelude         hiding (subst1)
import           Prelude              hiding (log)

-- The first session is the potential annotation.
-- The second session is inferred or absent.
checkOptSession :: Print channel => channel -> Maybe RSession -> Maybe RSession -> TC ()
checkOptSession c ms0 ms1 =
  case ms0 of
    Nothing -> return ()
    Just s0 ->
      case ms1 of
        Nothing -> checkUnused c Nothing s0
        Just s1 -> checkRSession s0 >> checkEqSessions c s0 s1

checkProc :: Proc -> TC Proto
checkProc (pref `Dot` procs) =
  checkPrefWellFormness pref >>
  checkVarDecs (pref >>= actVarDecs) (checkProcs procs) >>= checkPref pref

sendRecvSession :: Act -> TC (Channel, Session -> Session)
sendRecvSession = \case
  -- TODO this cannot infer dependent sends!
  -- https://github.com/np/ling/issues/13
  Send c e -> (,) c . sendS <$> inferTerm' e
  Recv c arg@(Arg _c typ) ->
    checkTyp typ $> (c, depRecv arg)
  _ -> tcError "typeSendRecv: Not Send/Recv"

checkPref :: Pref -> Proto -> TC Proto
checkPref pref proto
  | null pref =
      return proto
  | [act] <- pref =
      checkAct act proto
  | all isSendRecv pref = do
      css <- mapM sendRecvSession pref
      let proto' = protoSendRecv css proto
      debug . unlines $
        [ "Checking parallel prefix: `" ++ pretty (pref `Dot` []) ++ "`"
        , "Inferred protocol for the sub-process:"
        ] ++ prettyProto proto ++
        [ "Inferred protocol for the whole process:"
        ] ++ prettyProto proto'
      return proto'
  | otherwise =
      tcError $ "Unsupported parallel prefix " ++ pretty pref

checkProcs :: [Proc] -> TC Proto
checkProcs procs = mconcat <$> traverse checkProc procs

checkChanDec :: Proto -> ChanDec -> TC RSession
checkChanDec proto (Arg c s) = checkOptSession c s s' $> defaultEndR s'
  where s' = proto ^. chanSession c

checkRFactor :: RFactor -> TC ()
checkRFactor (RFactor t) = checkTerm intTyp t

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
checkAct :: Act -> Proto -> TC Proto
checkAct act proto =
  debugCheck (\proto' -> unlines $
              [ "Checking act `" ++ pretty act ++ "`"
              , "Inferred protocol for the sub-process:"
              ] ++ prettyProto proto ++
              [ "Inferred protocol for the whole process:"
              ] ++ prettyError prettyProto proto') $
  case act of
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
      -- This rmChans is potentially partly redundant.
      -- We might `assert` that `ds` is no longer in the `skel`
      rmChans ds <$> checkConflictingChans proto Nothing ds
    Split k c dOSs -> do
      assertAbsent c proto
      let ds         = dOSs^..each.argName
          dsSessions = defaultEndR <$> chanSessions ds proto
          s          = array k dsSessions
      for_ dOSs $ checkChanDec proto
      proto' <-
        case k of
          TenK -> checkConflictingChans proto (Just c) ds
          ParK -> checkSomeOrderChans proto (l2s ds) $> proto
          SeqK -> checkOrderedChans proto ds $> proto
      return $ substChans (ds, (c,oneS s)) proto'
    Send{} ->
      (`protoSendRecv` proto) . pure <$> sendRecvSession act
    Recv{} ->
      (`protoSendRecv` proto) . pure <$> sendRecvSession act
    NewSlice cs r _i -> do
      checkRFactor r
      ifor_ (proto^.chans) (checkSlice (`notElem` cs))
      return $ replProtoWhen (`elem` cs) r proto
    Ax s cs -> return $ protoAx s cs `dotProto` proto
    At e p -> do
      t <- inferTerm' e
      case t of
        TProto ss -> do
          proto' <- checkCPatt (wrapSessions ss) p
          return $ proto' `dotProto` proto
        _ ->
          tcError . unlines $ ["Expected a protocol type, not:", pretty t]

checkCPatt :: Session -> CPatt -> TC Proto
checkCPatt s = \case
  ChanP cd ->
    let proto = pureProto (cd^.argName) s in
    checkChanDec proto cd $> proto
  ArrayP kpat pats ->
    case s of
      Array k ss -> do
        assert (kpat == k)
          ["Expected an array splitting pattern with " ++ kindSymbols kpat ++
           " not " ++ kindSymbols k]
        assert (length pats == length ss)
          ["Expected " ++ show (length ss) ++ " sub-patterns, not " ++
            show (length pats)]
        arrayProto k <$> zipWithM checkCPattR ss pats
      _ ->
        tcError $ "Unexpected array splitting pattern (" ++
                  kindSymbols kpat ++ ") for session " ++ pretty s

checkCPattR :: RSession -> CPatt -> TC Proto
checkCPattR (s `Repl` r) pat
  | Just 1 <- isLitR r = checkCPatt s pat
  | otherwise          = tcError "Unexpected pattern for replicated session"

inferBranch :: (name,Term) -> TC (name,Scoped Typ)
inferBranch (n,t) = (,) n <$> inferTerm t

inferTerm' :: Term -> TC Typ
inferTerm' = fmap unScoped . inferTerm

inferTerm :: Term -> TC (Scoped Typ)
inferTerm e0 = debug ("Inferring type of " ++ pretty e0) >> case e0 of
  Lit l           -> return . emptyScope $ literalType l
  TTyp            -> return sTyp -- type-in-type
  Def x es        -> inferDef x es
  Lam arg t       -> sFun arg <$> checkVarDec arg (inferTerm t)
  Con n           -> conType n
  Case t brs      -> join $ caseType t <$> inferTerm t <*> mapM inferBranch brs
  Proc cs proc    -> inferProcTyp cs proc
  TFun arg s      -> checkVarDec arg (checkTyp s) $> sTyp
  TSig arg s      -> checkVarDec arg (checkTyp s) $> sTyp
  TProto sessions -> for_ sessions checkRSession  $> sTyp
  TSession s      -> checkSession s               $> sSession

inferProcTyp :: [ChanDec] -> Proc -> TC (Scoped Typ)
inferProcTyp cds proc = do
  let cs  = _argName <$> cds
  proto <- checkProc proc
  rs <- forM cds $ checkChanDec proto
  let proto' = rmChans cs proto
  assert (proto' ^. isEmptyProto) $
    "These channels have not been introduced:" :
    prettyChanDecs proto'
  return . emptyScope $ TProto rs

checkTerm :: Typ -> Term -> TC ()
checkTerm = checkTerm' . emptyScope

checkTyp :: Typ -> TC ()
checkTyp = checkTerm TTyp

checkTerm' :: Scoped Typ -> Term -> TC ()
checkTerm' expectedTyp e = do
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

checkSig :: Maybe Typ -> Maybe Term -> TC Typ
checkSig (Just typ) mtm = checkTyp typ >> checkMaybeTerm typ mtm $> typ
checkSig Nothing    mtm =
  case mtm of
    Just tm -> inferTerm' tm
    Nothing -> tcError "IMPOSSIBLE signature with no type nor definition"

inferDef :: Name -> [Term] -> TC (Scoped Typ)
inferDef (Name "_:_") [a,t] = do
  checkTyp a
  let a' = emptyScope a
  checkTerm' a' t
  return a'
inferDef f es = do
  mtyp  <- view $ evars . at f
  defs  <- view edefs
  case mtyp of
    Just typ -> checkApp f 0 (Scoped defs typ) es
    Nothing  -> tcError $ "unknown definition " ++ unName f ++
                          if f == anonName then
                            "\n\nHint: While `_` is allowed as a name for a definition, one cannot reference it."
                          else
                            ""

-- `checkApp f n typ es`
-- `f`   is the name of the definition currently checked
-- `n`   number of already checked arguments
-- `typ` the type of definition (minus the previously checked arguments)
-- `es`  the list of arguments
checkApp :: Name -> Int -> Scoped Typ -> [Term] -> TC (Scoped Typ)
checkApp _ _ typ []     = return typ
checkApp f n typ (e:es) =
  case reduceWHNF typ of
    (Scoped defs _typ@(TFun (Arg x ty) s)) -> do
      debug . unlines $
        ["Check application:"
        ,"f:      " ++ pretty f
        ,"ldefs:  " ++ pretty (typ ^. ldefs)
--        ,"ldefs': " ++ pretty defs
        ,"typ:    " ++ pretty (typ ^. scoped)
        ,"_typ:   " ++ pretty _typ
        ,"e:      " ++ pretty e
        ,"es:     " ++ pretty es
        {-
        ,"x:    " ++ pretty x
        ,"ty:   " ++ pretty ty
        ,"s:    " ++ pretty s
        -}
        ]
      checkTerm' (Scoped defs ty) e
      checkApp f (n + 1) (subst1 f (x, e) (Scoped defs s)) es
    _ -> tcError ("Too many arguments given to " ++ pretty f ++ ", " ++
                     show n ++ " arguments expected and " ++
                     show (n + 1 + length es) ++ " were given.")

checkRSession :: RSession -> TC ()
checkRSession (s `Repl` r) = checkSession s >> checkRFactor r

checkSession :: Session -> TC ()
checkSession s0 = case s0 of
  TermS _ t   -> checkTerm sessionTyp t
  IO _ arg s  -> checkVarDec arg $ checkSession s
  Array _ ss  -> for_ ss checkRSession

checkVarDef :: Name -> Maybe Typ -> Maybe Term -> Endom (TC a)
checkVarDef x mtyp mtm kont
  | x == anonName = checkSig mtyp mtm >> kont
  | otherwise     = do
    checkNotIn evars "name" x
    typ <- checkSig mtyp mtm
    local ((evars . at x .~ Just typ)
         . (edefs . at x .~ mtm)) kont

checkVarDec :: VarDec -> Endom (TC a)
checkVarDec (Arg x typ) = checkVarDef x (Just typ) Nothing

-- Check a "telescope", where bindings scope over the following ones
checkVarDecs :: [VarDec] -> Endom (TC a)
checkVarDecs = composeMap checkVarDec
