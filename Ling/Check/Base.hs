{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE TemplateHaskell            #-}

module Ling.Check.Base where

import           Ling.Defs
import           Ling.Equiv
import           Ling.ErrM
import           Ling.Norm
import           Ling.Prelude
import           Ling.Print
import           Ling.Reduce
import           Ling.Rename
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst   (Subst, substScoped)

import qualified Data.Set     as Set

{----------}
{- TCOpts -}
{----------}

data TCOpts = TCOpts
  { _debugChecker
  , _strictPar :: !Bool
  {- ^ No mix rule, {c,d} means that one can use c before d or
       d before c but not in parallel -}
  }

$(makeLenses ''TCOpts)

defaultTCOpts :: TCOpts
defaultTCOpts = TCOpts False False

{---------}
{- TCEnv -}
{---------}

data TCEnv = TCEnv
  { _tcOpts    :: !TCOpts
  , _evars     :: Map Name Typ
  -- ^ The type of term variables
  -- This includes the types for the defined:
  -- * terms
  -- * data types
  -- * data constructors
  , _edefs     :: Defs
  -- ^ Term definitions
  -- This holds not only the global definitions but also the local
  -- definitions (using `let`). However `local` (from MonadState) is
  -- used to keep the local definitions local.
  -- Type checking should return well-scoped terms. Namely the local
  -- definitions should be part of the definitions within 'Scoped'.
  , _ddefs     :: Map DataTypeName [Name]
  -- ^ Datatypes definitions
  , _ctyps     :: Map ConName DataTypeName
  -- ^ Data constructor ↦ type name
  }

makeLenses ''TCEnv

emptyTCEnv :: TCEnv
emptyTCEnv = TCEnv defaultTCOpts ø ø ø ø

tcEqEnv :: MonadReader TCEnv m => m EqEnv
tcEqEnv = eqEnv edefs

verbosity :: Lens' TCEnv Verbosity
verbosity = tcOpts . debugChecker

whenDebug :: MonadReader TCEnv m => m () -> m ()
whenDebug f = do
  v <- view verbosity
  when v f

debug :: MonadReader TCEnv m => Msg -> m ()
debug s = do
  v <- view verbosity
  debugTraceWhen v s (return ())

{---------}
{- TCErr -}
{---------}

type TCErr = String

tcError :: MonadError TCErr m => String -> m a
tcError = throwError -- . TCErr

assert :: MonadError TCErr m => Bool -> [Msg] -> m ()
assert True  _    = return ()
assert False msgs = tcError (unlines msgs)

assertDoc :: MonadError TCErr m => Bool -> Doc -> m ()
assertDoc True  _ = return ()
assertDoc False d = tcError (render d)

checkNoDups :: (Print a, Eq a, MonadError TCErr m) => String -> [a] -> m ()
checkNoDups _   [] = return ()
checkNoDups msg (x:xs)
  | x `elem` xs = tcError $ pretty x ++ " appears twice " ++ msg
  | otherwise   = checkNoDups msg xs

checkDisjointness :: (MonadError TCErr m, Print a, Ord a)
                  => String -> Fold s a -> [s] -> m ()
checkDisjointness k f s =
  assert (Set.null rs) ["These " ++ k ++ " should not be used in different parallel parts:"
                       ,pretty (s2l rs)]
  where
    ss = setOf f <$> s
    rs = redundant ss

checkPrefWellFormness :: MonadError TCErr m => Pref -> m ()
checkPrefWellFormness (Prll pref) = do
  checkDisjointness "free channels"  freeChans  pref
  checkDisjointness "bound channels" boundChans pref
  checkDisjointness "bound names"    boundVars  pref

requireAnnotation :: (MonadError TCErr m, Print a)
                  => String -> a -> Maybe b -> m b
requireAnnotation k a = \case
  Nothing -> tcError $ unwords [ "Missing type annotation for", k, pretty a ]
  Just c  -> pure c


{---------}
{- Trace -}
{---------}

data Trace
  = IO_T RW Typ
  | SeqT [Trace]
  -- ^ both for [:S,T:] and S.T
  | AltT [Trace]
  deriving Eq

makePrisms ''Trace

seqT :: Iso' Trace [Trace]
seqT = iso fw bw where
  fw = \case
    SeqT ts -> ts
    t       -> [t]
  bw = \case
    [t] -> t
    ts  -> SeqT ts

altT :: Iso' Trace [Trace]
altT = iso fw bw where
  fw = \case
    AltT ts -> ts
    t       -> [t]
  bw = \case
    [t] -> t
    ts  -> AltT ts

-- Sequential semigroup
instance Semigroup Trace where
  t0 <> t1 = seqT # (t0 ^. seqT ++ t1 ^. seqT)

-- Sequential monoid
instance Monoid Trace where
  mempty = SeqT []

(<|>) :: Trace -> Trace -> Trace
t0 <|> t1 = altT # (t0 ^. altT ++ t1 ^. altT)

traceTypes :: Traversal' Trace Typ
traceTypes f = \case
  IO_T rw ty -> IO_T rw <$> f ty
  SeqT ts    -> (seqT #) <$> (traverse . traceTypes) f ts
  AltT ts    -> (altT #) <$> (traverse . traceTypes) f ts

-- traceHasInitRead == traceRW ((==) [Read] . take 1)
traceHasInitRead :: [Trace] -> Bool
traceHasInitRead = \case
  []              -> False
  IO_T rw _  : _  -> rw == Read
  SeqT ts'   : ts -> traceHasInitRead (ts' ++ ts)
  AltT ts'   : ts -> any (\t -> traceHasInitRead (t : ts)) ts'

traceRW :: ([RW] -> Bool) -> [Trace] -> Bool
traceRW f = \case
  []              -> f []
  IO_T rw _  : ts -> traceRW (f . (rw:)) ts
  SeqT ts'   : ts -> traceRW f (ts' ++ ts)
  AltT ts'   : ts -> any (\t -> traceRW f (t : ts)) ts'

{-----------}
{- Session -}
{-----------}

type IsSession a = (HasEquiv a, Dual a)

checkEqSessions :: (IsSession s, MonadTC m, Print channel)
                => channel -> Scoped s -> Scoped s -> m ()
checkEqSessions c s0 s1 =
  checkEquivalence
    ("On channel " ++ pretty c ++ " sessions are not equivalent.")
    "Given session (expanded):" s0
    "Inferred session:"         s1

checkOneR :: MonadError TCErr m => RFactor -> m ()
checkOneR r = assert (r == ø) ["Unexpected replication:", pretty r]

-- Prop: isSource . log = const True
-- A source is only made of sends but can be combined with any form of
-- array: Seq, Par, Ten.
isSource :: (MonadTC m, IsSession a) => a -> m Bool
isSource x = view _1 <$> isEquiv (pure (send_ s)) (pure s)
  where s = seq_ x

isSink :: (MonadTC m, IsSession a) => a -> m Bool
isSink = isSource . dual

validAx :: (MonadTC m, IsSession a) => a -> [channel] -> m Bool
-- Forwarding anything between no channels is always possible
validAx _ []          = pure True
-- At least two for the general case
validAx _ (_ : _ : _) = pure True
-- One is enough if the session is a Sink. A sink can be derived
-- alone. Another way to think of it is that in the case of a sink,
-- the other side is a Log and there can be any number of Logs.
validAx s (_ : _)     = isSink s

checkDual2 :: MonadTC m => RSession -> RSession -> m ()
checkDual2 (s0 `Repl` r0) (s1 `Repl` r1) = do
  checkOneR r0
  checkOneR r1
  (b, us0, us1) <- isEquiv (pure s0) (pure (dual s1))
  assertDiff
    "Sessions are not dual." (\_ _ -> b)
    "Given session (expanded):" us0
    "Inferred dual session:"    (dual us1)

-- Unlike checkDual2, checkCompat2 does not care about the kind of array
-- being used. The only constraint is that sends must match recvs.
checkCompat2 :: MonadTC m => RSession -> RSession -> m ()
checkCompat2 rs0 rs1 = checkDual2 (seq_ rs0) (seq_ rs1)

{-
[: Si, S ^ n, So :]

Si <-> S
S <-> So
Si <-> So
S <-> S
isSource Si
isSink So

---------
?A <-> !A

S <-> T
-----------
?A. S <-> T

---
What about using the same channel name for:
  `new [: c : !A, c : ?A :]` ?

Issue is that the inferred session is going to be
  c : !A. ?A
---

new (c : A)

new [: !A, (?A.!A)^ n, ?A :]

[: !A, [: ?A, !A :]^ n, ?A :]

S = [: !A, !B :]
[: S, [: ~S, S :]^ n, ~S* :]
-}

checkDual :: MonadTC m => [RSession] -> m ()
checkDual [] = pure ()
checkDual [s0, s1] = checkDual2 s0 s1
checkDual _ = error "checkDual: too many channels"

type AllocAnnots = [Term]

-- As soon as we do support more features than fusion,
-- this function would check that alloc is used but would allow the other
-- annotations.
isAllocated :: MonadTC m => AllocAnnots -> m Bool
isAllocated = fmap (view _1) . isEquiv (pure [mkPrimOp (Name "alloc") []]) . pure

hasDupWrites :: [RW] -> Bool
hasDupWrites = \case
  []                  -> False
  Read  : rws         -> hasDupWrites rws
  Write : []          -> False
  Write : Read  : rws -> hasDupWrites rws
  Write : Write : _   -> True

hasManyWrites :: [RW] -> Bool
hasManyWrites = (== 2) . length . take 2 . filter (== Write)

checkNewChan :: (MonadTC m, Print channel) => AllocAnnots -> channel -> RSession -> Maybe Typ -> m ()
checkNewChan anns c rs mty = do
  scrs <- tcScope rs
  tr <- newChanRSession c scrs
  checkTypesEquivalence (mty ^.. _Just ++ tr ^.. traceTypes)
  -- So far we consider that write,read,write,read,... needs an allocation however at fusion
  -- steps could be made:
  -- new (c : Int). c <- 1. let x <- c. c <- (x + x). let y <- c
  -- could be fused one step as:
  -- let x = 2. new (c : Int). c <- (x + x). let y <- c
  when (traceHasInitRead [tr]) $
    tcError . concat $ ["Unexpected read on the freshly allocated channel ", pretty c]
  when (traceRW hasDupWrites [tr]) $
    tcError . concat $ ["Unexpected consecutive writes on the allocated channel ", pretty c]
  isAlloc <- isAllocated anns
  when (not isAlloc && traceRW hasManyWrites [tr]) $
    tcError . concat $ ["Too many writes on the allocated (without /alloc) channel ", pretty c]

type NewChan a = forall channel m. (MonadError TCErr m, Print channel) => channel -> a -> m Trace

newChanSession :: NewChan (Scoped Session)
newChanSession c scs = do
  let rss = reduce scs ^. reduced
  case rss ^. scoped of
    IO rw1 (Arg _ mty1) s1 -> do
      let ty1 = mkLetS $ rss $> (mty1 ?| error "IMPOSSIBLE: inferred session must have type annotations")
      (IO_T rw1 ty1 <>) <$> newChanSession c (scs *> rss $> s1)
    Array k (Sessions ss) ->
      case k of
        SeqK -> (seqT #) <$> mapM (newChanRSession c . (scs *> rss $>)) ss
        _    ->
             -- It could make sense to allow par/ten in read only.
             -- One could a tree instead of a list of (RW,Typ)...
                tcError . concat $
                  ["Unexpected array session (", pretty (substScoped scs), ") when "
                  ,"allocating channel ", pretty c, ".\n"
                  ,"To allocate an array use `new [c:S,c':~S]` or `new [:c:S,c':~S:]`"]
    TermS{} -> tcError . concat $
                  ["Unsupported abstract session (", pretty (substScoped scs), ") when "
                  ,"allocating channel ", pretty c, "."]

-- The replication here is meant to be of kind SeqK.
newChanRSession :: NewChan (Scoped RSession)
newChanRSession c scrs =
  case scrs ^. scoped of
    s `Repl` r -> do
      tr <- newChanSession c (scrs $> s)
      case reduce (scrs $> r) ^? reduced . scoped . litR . integral of
        Just n  -> pure . mconcat $ replicate n tr
        Nothing -> pure $ AltT [ø, tr, tr <> tr]

{-----------}
{- MonadTC -}
{-----------}

type MonadTC m = (MonadReader TCEnv m, MonadError TCErr m)
type HasEquiv a = (Print a, Eq a, Equiv a, Subst a)

isEquiv :: (HasEquiv a, MonadTC m) => Scoped a -> Scoped a -> m (Bool, a, a)
isEquiv t0 t1 = do
  env <- tcEqEnv
  sco <- tcScope ()
  let
    ut0 = substScoped $ sco *> t0
    ut1 = substScoped $ sco *> t1
  whenDebug $
    when (t0 /= t1) $ do
      debug . unlines $
        ["checkEquivalence:", "  " ++ pretty t0, "against", "  " ++ pretty t1]
      when (ut0 == ut1) . debug . unlines $
        ["Once expanded they are equal:", pretty ut0]
  return (equiv env t0 t1, ut0, ut1)

checkEquivalence :: (HasEquiv a, MonadTC m) => String -> String -> Scoped a -> String -> Scoped a -> m ()
checkEquivalence msg expected t0 inferred t1 = do
  (b, ut0, ut1) <- isEquiv t0 t1
  assertDiff msg (\_ _ -> b) expected ut0 inferred ut1

assertDiff :: (MonadError TCErr m, Print a)
           => String -> Rel a
           -> String -> a
           -> String -> a
           -> m ()
assertDiff msg cond expected x0 inferred x1 =
  assert (cond x0 x1) [msg, expected, "  " ++ pretty x0, inferred, "  " ++ pretty x1]

checkTypeEquivalence :: MonadTC m => Typ -> Typ -> m ()
checkTypeEquivalence t0 t1 =
   checkEquivalence "Types are not equivalent."
                    "Expected:" (pure t0)
                    "Inferred:" (pure t1)

checkTypesEquivalence :: MonadTC m => [Typ] -> m ()
checkTypesEquivalence = \case
  [] -> pure ()
  [_] -> pure ()
  t0 : t1 : ts -> checkTypeEquivalence t0 t1 >> checkTypesEquivalence (t1 : ts)

checkNotIn :: (Ord name, Print name, MonadTC m) => Getter TCEnv (Map name v) -> String -> name -> m ()
checkNotIn l msg c = do
  b <- view $ l . hasKey c
  assert (not b) ["Already defined " ++ msg ++ ": ", pretty c]

conTypeName :: MonadTC m => Name -> m Name
conTypeName c =
  maybe (tcError $ "No such constructor " ++ pretty c) return =<< view (ctyps . at c)

debugCheck :: MonadTC m => (Err a -> String) -> Endom (m a)
debugCheck fmt k =
  (do x <- k
      debug (fmt (Ok x))
      return x
  ) `catchError` \err ->
   do debug (fmt (Bad err))
      throwError err

errorScope :: (Print name, MonadError TCErr m) => name -> Endom (m a)
errorScope = errorScope' . ("While checking `" ++) . (++ "`") . pretty

errorScope' :: (MonadError TCErr m) => String -> Endom (m a)
errorScope' msg ma =
  ma `catchError` \err -> throwError . unlines $ msg : err ^.. indented 2

{-----------------------}
{- Basic type checking -}
{-----------------------}

literalType :: Literal -> Typ
literalType = \case
  LInteger{} -> intTyp
  LDouble{}  -> doubleTyp
  LChar{}    -> charTyp
  LString{}  -> stringTyp

tcScope :: MonadReader TCEnv m => a -> m (Scoped a)
tcScope a = (\x -> Scoped x ø a) <$> view edefs

tcReduce :: (MonadReader TCEnv m, HasReduce a b) => a -> m (Scoped b)
tcReduce a = view reduced . reduce <$> tcScope a

caseType :: MonadTC m => Term -> Typ -> [(Name, Typ)] -> m Typ
caseType t ty brs = do
  sty <- tcReduce ty
  let err = tcError $ "Case on a non data type: " ++ pretty (substScoped sty)
  case sty ^. scoped of
    Def _{-Undefined ?-} d [] -> do
      def <- view $ ddefs . at d
      case def of
        Just cs -> do
          assertDiff "Labels are not equal." (==)
                     "Expected:" (Comma (sort cs))
                     "Inferred:" (Comma (fst <$> brs))

          env <- tcEqEnv
          return $ mkCaseBy id (equiv env) t brs
        _ -> err
    _ -> err

conType :: MonadTC m => Name -> m Typ
conType = fmap mkTyCon0 . conTypeName

-- When we are guaranteed to allocate we use checkCompat2 instead of checkDual2 internally.
-- This allows this kind of examples:
-- * new/alloc [: cd: {  !Int,!Bool  }, ef: { ?Int,?Bool } :]
-- * new/alloc [: cd: [  !Int,!Bool  ], ef: [ ?Int,?Bool ] :]
-- * new/alloc [: cd: [: !Int,!Bool :], ef: { ?Int,?Bool } :]
-- * new/alloc [: cd: {  !Int,!Bool  }, m : [: {?Int,?Bool},{!Int,!Bool} :]^n, ef: { ?Int,?Bool } :]
-- and so on.
-- All of them would have been reject without /alloc.
-- This is justified by the fact that the first session is a source,
-- and thus all the writes happens before the reads.
checkSeqNew :: MonadTC m => AllocAnnots -> [(Channel, RSession)] -> m ()
checkSeqNew anns = \case
  []                      -> pure ()
  (c0, s0 `Repl` r0):crs0 -> do
    errorScope c0 $ do
      b <- isSource s0
      checkOneR r0
      assert b
        ["Sequential `new` expects the session for channel " ++
        pretty c0 ++
        " to be made of sends (a Log)"
        ,pretty s0]
    isAlloc <- isAllocated anns
    go isAlloc (oneS s0) crs0
  where
    go isAlloc rs0 = \case
      (c1, s1 `Repl` r1):crs1
        | r1 /= ø
          -- TODO use reduce on s1
        , Array SeqK (Sessions [s1L, s1R]) <- s1 -> do
            assert isAlloc ["Expecting a /alloc annotation"]
            errorScope c1 $ do
              checkCompat2 rs0 s1L
              checkCompat2 s1L s1R
            go isAlloc rs0 crs1
      crs
        | isAlloc ->
            forM_ crs $ \(c, rs) ->
              errorScope c $ checkCompat2 rs0 (rs & rfactor .~ litR1 # ())
        | otherwise ->
            forM_ crs $ \(c, rs) ->
              errorScope c $ checkDual2 rs0 rs


{------}
{- TC -}
{------}

newtype TC a = MkTC { unTC :: ReaderT TCEnv (Except TCErr) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadReader TCEnv, MonadError TCErr)

instance Semigroup a => Semigroup (TC a) where
  (<>) = liftM2 (<>)

instance Monoid a => Monoid (TC a) where
  mempty = pure mempty

runTCEnv :: TCEnv -> TC a -> Err a
runTCEnv env tc = either Bad Ok
                . runExcept
                $ runReaderT (unTC tc) env

runTCOpts :: TCOpts -> TC a -> Err a
runTCOpts opts = runTCEnv $ emptyTCEnv & tcOpts .~ opts
-- -}
