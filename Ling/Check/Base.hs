{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE TemplateHaskell            #-}
module Ling.Check.Base where

import           Ling.Equiv
import           Ling.ErrM
import           Ling.Free
import           Ling.Norm
import           Ling.Print
import           Ling.Reduce
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst           (Subst, unScoped)
import           Ling.Prelude         hiding (subst1)

import qualified Data.Set             as Set

------------
-- TCOpts --
------------

data TCOpts = TCOpts
  { _debugChecker
  , _strictPar :: !Bool
  -- ^ No mix rule, {c,d} means that one can use c before d or
  -- d before c but not in parallel
  }

$(makeLenses ''TCOpts)

defaultTCOpts :: TCOpts
defaultTCOpts = TCOpts False False

-----------
-- TCEnv --
-----------

data TCEnv = TCEnv
  { _tcOpts    :: !TCOpts
  , _evars     :: Map Name Typ
  -- ^ Term types
  , _edefs     :: Map Name Term
  -- ^ Term definitions
  , _ddefs     :: Map Name [Name]
  -- ^ Datatypes definitions
  , _ctyps     :: Map Name Name
  -- ^ Data constructor ↦ type name
  }

$(makeLenses ''TCEnv)

emptyTCEnv :: TCEnv
emptyTCEnv = TCEnv defaultTCOpts ø ø ø ø

tcEqEnv :: MonadReader TCEnv m => m EqEnv
tcEqEnv = emptyEqEnv <$> view edefs

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

-----------
-- TCErr --
-----------

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
  | x `elem` xs    = tcError $ pretty x ++ " appears twice " ++ msg
  | otherwise      = checkNoDups msg xs

checkDisjointness :: (MonadError TCErr m, Ord a) => String -> [Set a] -> m ()
checkDisjointness k ss =
  assert (Set.null rs)
    ["These " ++ k ++ " should not be used in different parallel parts" ]
  where rs = redundant ss

checkPrefWellFormness :: MonadError TCErr m => Pref -> m ()
checkPrefWellFormness pref = do
  checkDisjointness "free channels"  $ fcAct <$> pref
  checkDisjointness "bound channels" $ bcAct <$> pref
  checkDisjointness "bound names"    $ bvAct <$> pref

checkEqSessions :: MonadTC m =>
                   Name -> RSession -> Maybe RSession -> m ()
checkEqSessions c s0 Nothing   = checkUnused c Nothing s0
checkEqSessions c s0 (Just s1) =
  checkEquivalence
    ("On channel " ++ pretty c ++ " sessions are not equivalent.")
    "Given session (expanded):" (emptyScope s0)
    "Inferred session:"         (emptyScope s1)

-- checkUnused c ms s: Check if the channel c is used given the
-- inferred session ms, and its dual ds.
checkUnused :: MonadError TCErr m =>
               Name -> Maybe RSession -> RSession -> m ()
checkUnused _ (Just _) _ = return ()
checkUnused c Nothing  s = assert (isEndR s) ["Unused channel " ++ pretty c]

checkOneR :: MonadError TCErr m => RFactor -> m ()
checkOneR r = assert (r == ø) ["Unexpected replication:", pretty r]

checkDual :: MonadTC m => RSession -> RSession -> m ()
checkDual (Repl s0 r0) (Repl s1 r1) = do
  checkOneR r0
  checkOneR r1
  (b, us0, us1) <- isEquiv (emptyScope s0) (emptyScope (dual s1))
  assertDiff
    "Sessions are not dual." (\_ _ -> b)
    "Given session (expanded):" us0
    "Inferred dual session:"    (dual us1)

checkSlice :: MonadError TCErr m => (Channel -> Bool) -> Channel -> RSession -> m ()
checkSlice cond c (s `Repl` r) = when (cond c) $ do
  checkOneR r
  assert (allSndRcv s) ["checkSlice: non send/recv session"]

-------------
-- MonadTC --
-------------

type MonadTC m = (MonadReader TCEnv m, MonadError TCErr m)

isEquiv :: (Print a, Eq a, Equiv a, Subst a, MonadTC m)
        => Scoped a -> Scoped a -> m (Bool, a, a)
isEquiv t0 t1 = do
  env <- tcEqEnv
  whenDebug $ do
    when (t0 /= t1) . debug . unlines $
      ["checkEquivalence:"
      ,"  " ++ pretty t0
      ,"against"
      ,"  " ++ pretty t1
      ]
    when (ut0 == ut1) . debug . unlines $
      ["Once expanded they are equal"]
  return (equiv env t0 t1, ut0, ut1)
  where ut0 = unScoped t0
        ut1 = unScoped t1

checkEquivalence :: (Print a, Eq a, Equiv a, Subst a, MonadTC m)
                 => String -> String -> Scoped a -> String -> Scoped a -> m ()
checkEquivalence msg expected t0 inferred t1 = do
  (b, ut0, ut1) <- isEquiv t0 t1
  assertDiff msg (\_ _ -> b) expected ut0 inferred ut1

assertDiff :: (MonadError TCErr m, Print a)
           => String -> (a -> a -> Bool)
           -> String -> a
           -> String -> a
           -> m ()
assertDiff msg cond expected x0 inferred x1 =
  assert (cond x0 x1)
    [msg
    ,expected
    ,"  " ++ pretty x0
    ,inferred
    ,"  " ++ pretty x1
    ]

checkTypeEquivalence :: MonadTC m => Scoped Typ -> Scoped Typ -> m ()
checkTypeEquivalence t0 t1 =
   checkEquivalence "Types are not equivalent."
                    "Expected:" t0
                    "Inferred:" t1

checkNotIn :: MonadTC m => Lens' TCEnv (Map Name v) -> String -> Name -> m ()
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

-------------------------
-- Basic type checking --
-------------------------

literalType :: Literal -> Typ
literalType l = case l of
  LInteger{} -> intTyp
  LDouble{}  -> doubleTyp
  LChar{}    -> charTyp
  LString{}  -> stringTyp

caseType :: MonadTC m => Term -> Scoped Typ -> [(Name,Scoped Typ)] -> m (Scoped Typ)
caseType t ty brs =
  case reduceWHNF ty ^. scoped of
    Def d [] -> do
      def <- view $ ddefs . at d
      case def of
        Just cs -> do
          assertDiff "Labels are not equal." (==)
                     "Expected:" (Comma (sort cs))
                     "Inferred:" (Comma (fst <$> brs))

          env <- tcEqEnv
          return $
            fromMaybe (emptyScope (mkCase t (brs & mapped . _2 %~ unScoped)))
                      (theUniqBy (equiv env) (snd <$> brs))
        _ -> tcError $ "Case on a non data type: " ++ pretty d
    _ -> tcError $ "Case on a non data type: " ++ pretty (ty^.scoped)

def0 :: Name -> Term
def0 x = Def x []

conType :: MonadTC m => Name -> m (Scoped Typ)
conType = fmap (emptyScope . def0) . conTypeName

sTyp :: Scoped Typ
sTyp = emptyScope TTyp

sFun :: VarDec -> Scoped Typ -> Scoped Typ
sFun arg s
  | s^.ldefs.hasKey(arg^.argName) = error "sFun: IMPOSSIBLE"
  | otherwise                     = TFun arg <$> s

sSession :: Scoped Typ
sSession = emptyScope sessionTyp

--------
-- TC --
--------

newtype TC a = MkTC { unTC :: ReaderT TCEnv (Except TCErr) a }
  deriving (Functor, Applicative, Monad, MonadReader TCEnv, MonadError TCErr)

runTC :: TCOpts -> TC a -> Err a
runTC opts tc = either Bad Ok
              . runExcept
              . runReaderT (unTC tc)
              $ emptyTCEnv & tcOpts .~ opts
