{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE TemplateHaskell            #-}
module Ling.Check.Base where

import           Ling.Constraint
import           Ling.Equiv
import           Ling.ErrM
import           Ling.Norm
import           Ling.Print
import           Ling.Proto
import           Ling.Scoped
import           Ling.Session
import           Ling.Subst                (Subst, unScoped)
import           Ling.Utils                hiding (subst1)

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.List                 (sort)
import           Data.Map                  (Map, empty)
import qualified Data.Set                  as Set

data TCEnv = TCEnv
  { _verbosity :: Verbosity
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
emptyTCEnv = TCEnv False empty empty empty empty

newtype TC a = MkTC { unTC :: ReaderT TCEnv Err a }
  deriving (Functor, Applicative, Monad, MonadReader TCEnv)

instance MonadError String TC where
  throwError = MkTC . lift . Bad
  catchError = error "catchError: not implemented for TC"

checkEquality :: (Print a, Eq a) => String -> a -> a -> TC ()
checkEquality msg t0 t1 = assertEqual t0 t1
  [msg
  ,"Expected:"
  ,"  " ++ pretty t0
  ,"Inferred:"
  ,"  " ++ pretty t1
  ]

tcEqEnv :: TC EqEnv
tcEqEnv = emptyEqEnv <$> view edefs

checkEquivalence :: (Print a, Eq a, Equiv a, Subst a)
                 => String -> Scoped a -> Scoped a -> TC ()
checkEquivalence msg t0 t1 = do
  env <- tcEqEnv
  whenDebug $ do
    when (t0 /= t1) . debug $
      ["checkEquivalence:"
      ,"  " ++ pretty t0
      ,"against"
      ,"  " ++ pretty t1
      ]
    when (ut0 == ut1) . debug $
      ["Once expanded they are equal"]
  assert (equiv env t0 t1)
    [msg
    ,"Expected:"
    ,"  " ++ pretty ut0
    ,"Inferred:"
    ,"  " ++ pretty ut1
    ]
  where ut0 = unScoped t0
        ut1 = unScoped t1

checkTypeEquivalence :: Scoped Typ -> Scoped Typ -> TC ()
checkTypeEquivalence = checkEquivalence "Types are not equivalent."

checkNotIn :: Lens' TCEnv (Map Name v) -> String -> Name -> TC ()
checkNotIn l msg c = do
  b <- view $ l . hasKey c
  assert (not b) ["Already defined " ++ msg ++ ": ", pretty c]

checkNoDups :: (Print a, Eq a) => String -> [a] -> TC ()
checkNoDups _   [] = return ()
checkNoDups msg (x:xs)
  | x `elem` xs    = throwError $ pretty x ++ " appears twice " ++ msg
  | otherwise      = checkNoDups msg xs

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

caseType :: Term -> Scoped Typ -> [(Name,Scoped Typ)] -> TC (Scoped Typ)
caseType t ty brs =
  case unDef ty ^. scoped of
    Def d [] -> do
      def <- view $ ddefs . at d
      case def of
        Just cs -> do
          checkEquality "Labels are not equal." (sort cs) (fst <$> brs)
          env <- tcEqEnv
          return $ if allEquiv env (snd <$> brs) then snd (head brs)
                   else emptyScope (Case t (brs & mapped . _2 %~ unScoped))
        _ -> throwError $ "Case on a non data type: " ++ pretty d
    _ -> throwError $ "Case on a non data type: " ++ pretty (ty^.scoped)

conTypeName :: Name -> TC Name
conTypeName c =
  maybe (throwError $ "No such constructor " ++ pretty c) return =<< view (ctyps . at c)

def0 :: Name -> Term
def0 x = Def x []

conType :: Name -> TC (Scoped Typ)
conType = fmap (emptyScope . def0) . conTypeName

sTyp :: Scoped Typ
sTyp = emptyScope TTyp

sFun :: VarDec -> Scoped Typ -> Scoped Typ
sFun arg s
  | s^.ldefs.hasKey(arg^.argName) = error "sFun: IMPOSSIBLE"
  | otherwise                     = TFun arg <$> s

whenDebug :: MonadReader TCEnv m => m () -> m ()
whenDebug f = do
  v <- view verbosity
  when v f

debug :: [Msg] -> TC ()
debug xs = do
  v <- view verbosity
  debugTraceWhen v xs (return ())

assert :: Bool -> [Msg] -> TC ()
assert True  _    = return ()
assert False msgs = throwError (unlines msgs)

assertDoc :: Bool -> Doc -> TC ()
assertDoc True  _ = return ()
assertDoc False d = throwError (render d)

assertEqual :: Eq a => a -> a -> [Msg] -> TC ()
assertEqual x y = assert (x == y)

data CheckOpts = CheckOpts { _debugChecker :: Bool }

$(makeLenses ''CheckOpts)

defaultCheckOpts :: CheckOpts
defaultCheckOpts = CheckOpts False

runTC :: CheckOpts -> TC a -> Err a
runTC opts tc = runReaderT (unTC tc) (emptyTCEnv & verbosity .~ (opts ^. debugChecker))
