{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Ling.Check.Core where

import           Ling.Check.Base
import           Ling.Norm
import           Ling.Print
import           Ling.Proto
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst           (unScoped)
import           Ling.Utils           hiding (subst1)
import           Prelude              hiding (log)

import           Control.Lens
import           Control.Monad        (join)
import           Control.Monad.Reader (local)

checkOptSession :: Name -> Maybe RSession -> Maybe RSession -> TC ()
checkOptSession _ Nothing   _   = return ()
checkOptSession c (Just s0) ms1 = checkRSession s0 >> checkEqSessions c s0 ms1

checkProc :: Proc -> TC Proto
checkProc (pref `Dot` procs) = do
  checkPrefWellFormness pref
  proto <- checkVarDecs (concatMap actVarDecs pref) $ checkProcs procs
  checkPref pref proto

sendRecvSession :: Act -> TC (Channel, Session -> Session)
sendRecvSession = \case
  Send c e -> (,) c . Snd <$> inferTerm' e
  Recv c (Arg _ typ) -> checkTyp typ >> return (c, Rcv typ)
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
checkChanDec proto (Arg c s) = checkOptSession c s s' >> return (defaultEndR s')
  where s' = proto ^. chanSession c

checkChanDecs_ :: Proto -> [ChanDec] -> TC ()
checkChanDecs_ = mapM_ . checkChanDec

checkChanDecs :: Proto -> [ChanDec] -> TC [RSession]
checkChanDecs = mapM . checkChanDec



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
      proto' <- checkConflictingChans proto ds
      return $ rmChans ds proto'
    Split k c dOSs -> do
      assertAbsent c proto
      let ds         = dOSs^..each.argName
          dsSessions = map defaultEndR $ chanSessions ds proto
          s          = array k dsSessions
      checkChanDecs_ proto dOSs
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
      typ <- inferTerm' e
      return $ protoSendRecv [(c, Snd typ)] proto
    Recv c (Arg _x typ) -> do
      checkTyp typ
      return $ protoSendRecv [(c, Rcv typ)] proto
    NewSlice cs t _i -> do
      checkTerm intTyp t
      mapM_ (checkSlice (`notElem` cs)) (proto ^. chans . to m2l)
      return $ replProtoWhen (`elem` cs) t proto
    Ax s cs -> return $ proto <> protoAx (one s) cs
    At e cs -> do
      t <- inferTerm' e
      case t of
        TProto ss -> do
          assertEqual (length cs) (length ss)
             ["Expected " ++ show (length ss) ++ " channels, not " ++ show (length cs)]
          return $ proto <> mkProto (zip cs ss)
        _ ->
          tcError . unlines $ ["Expected a protocol type, not:", pretty t]

inferBranch :: (Name,Term) -> TC (Name,Scoped Typ)
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
  TFun arg s      -> checkVarDec arg (checkTyp s) >> return sTyp
  TSig arg s      -> checkVarDec arg (checkTyp s) >> return sTyp
  TProto sessions -> checkSessions sessions       >> return sTyp

inferProcTyp :: [ChanDec] -> Proc -> TC (Scoped Typ)
inferProcTyp cds proc = do
  let cs  = map _argName cds
  proto <- checkProc proc
  rs <- checkChanDecs proto cds
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
checkSig (Just typ) mtm = checkTyp typ >> checkMaybeTerm typ mtm >> return typ
checkSig Nothing    mtm =
  case mtm of
    Just tm -> inferTerm' tm
    Nothing -> tcError "IMPOSSIBLE signature with no type nor definition"

inferDef :: Name -> [Term] -> TC (Scoped Typ)
inferDef f es = do
  mtyp  <- view $ evars . at f
  defs  <- view edefs
  case mtyp of
    Just typ -> checkApp f 0 (Scoped defs typ) es
    Nothing  -> tcError $ "unknown definition " ++ unName f

-- `checkApp f n typ es`
-- `f`   is the name of the definition currently checked
-- `n`   number of already checked arguments
-- `typ` the type of definition (minus the previously checked arguments)
-- `es`  the list of arguments
checkApp :: Name -> Int -> Scoped Typ -> [Term] -> TC (Scoped Typ)
checkApp _ _ typ []     = return typ
checkApp f n typ (e:es) =
  case unDef typ of
    (Scoped defs typ'@(TFun (Arg x ty) s)) -> do
      debug . unlines $
        ["Check application:"
        ,"f:      " ++ pretty f
        ,"ldefs:  " ++ pretty (typ ^. ldefs)
        ,"ldefs': " ++ pretty defs
        ,"typ:    " ++ pretty (typ ^. scoped)
        ,"typ':   " ++ pretty typ'
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

checkSessions :: [RSession] -> TC ()
checkSessions = mapM_ checkRSession

checkRSession :: RSession -> TC ()
checkRSession (Repl s t) = checkSession s >> checkTerm intTyp t

checkSession :: Session -> TC ()
checkSession s0 = case s0 of
  Atm _ n -> checkTerm sessionTyp (Def n [])
  End -> return ()
  Snd t s -> checkTyp t >> checkSession s
  Rcv t s -> checkTyp t >> checkSession s
  Par ss -> checkSessions ss
  Ten ss -> checkSessions ss
  Seq ss -> checkSessions ss

checkVarDef :: Name -> Maybe Typ -> Maybe Term -> Endom (TC a)
checkVarDef x mtyp mtm kont = do
  checkNotIn evars "name" x
  typ <- checkSig mtyp mtm
  local ((evars . at x .~ Just typ)
       . (edefs . at x .~ mtm)) kont

checkVarDec :: VarDec -> Endom (TC a)
checkVarDec (Arg x typ) = checkVarDef x (Just typ) Nothing

-- Check a "telescope", where bindings scope over the following ones
checkVarDecs :: [VarDec] -> Endom (TC a)
checkVarDecs = composeMap checkVarDec
