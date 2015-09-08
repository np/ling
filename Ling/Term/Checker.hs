{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE TemplateHaskell            #-}
module Ling.Term.Checker where

import           Ling.Abs                  (Name)
import           Ling.Equiv
import           Ling.ErrM
import           Ling.Norm
import           Ling.Print                hiding (render)
import           Ling.Proto
import qualified Ling.Rename               as Ren
import           Ling.Scoped
import           Ling.Subst                (Subst, unScoped)
import           Ling.Utils

import           Control.Applicative       hiding (empty)
import           Control.Lens
import           Control.Monad.Error.Class
import           Control.Monad.Reader
import           Data.List                 (sort)
import           Data.Map                  (Map, empty)

data ProcDef = ProcDef Name [ChanDec] Proc Proto

data TCEnv = TCEnv
  { _verbosity :: Verbosity
  , _evars     :: Map Name Typ
  -- ^ Term types
  , _edefs     :: Map Name Term
  -- ^ Term definitions
  , _pdefs     :: Map Name ProcDef
  -- ^ Processes definitions
  , _ddefs     :: Map Name [Name]
  -- ^ Datatypes definitions
  , _ctyps     :: Map Name Name
  -- ^ Data constructor ↦ type name
  }

$(makeLenses ''TCEnv)

emptyTCEnv :: TCEnv
emptyTCEnv = TCEnv False empty empty empty empty empty

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

checkTyp :: Typ -> TC ()
checkTyp = checkTerm TTyp

checkNotIn :: Lens' TCEnv (Map Name v) -> String -> Name -> TC ()
checkNotIn l msg c = do
  b <- view $ l . hasKey c
  assert (not b) ["Already defined " ++ msg ++ ": ", pretty c]

checkVarDef :: Name -> Typ -> Maybe Term -> Endom (TC a)
checkVarDef x typ mt kont = do
  checkNotIn evars "name" x
  checkTyp typ
  checkMaybeTerm typ mt
  local ((evars . at x .~ Just typ)
       . (edefs . at x .~ mt)) kont

checkVarDec :: VarDec -> Endom (TC a)
checkVarDec (Arg x typ) = checkVarDef x typ Nothing

-- Check a "telescope", where bindings scope over the following ones
checkVarDecs :: [VarDec] -> Endom (TC a)
checkVarDecs []     = id
checkVarDecs (d:ds) = checkVarDec d . checkVarDecs ds
-- checkVarDecs ds = foldrOf (...checkVarDec...) ds

-- TODO: Here I assume that sessions are well formed
checkSessions :: [RSession] -> TC ()
checkSessions = mapM_ checkRSession

checkRSession :: RSession -> TC ()
checkRSession (Repl s t) = checkSession s >> checkTerm int t

checkSession :: Session -> TC ()
checkSession s0 = case s0 of
  Atm _ n -> checkTerm tSession (Def n [])
  End -> return ()
  Snd t s -> checkTyp t >> checkSession s
  Rcv t s -> checkTyp t >> checkSession s
  Par ss -> checkSessions ss
  Ten ss -> checkSessions ss
  Seq ss -> checkSessions ss

checkNoDups :: (Print a, Eq a) => String -> [a] -> TC ()
checkNoDups _   [] = return ()
checkNoDups msg (x:xs)
  | x `elem` xs    = throwError $ pretty x ++ " appears twice " ++ msg
  | otherwise      = checkNoDups msg xs

inferCase :: Term -> Scoped Typ -> [(Name,Scoped Typ)] -> TC (Scoped Typ)
inferCase t ty brs =
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

inferBranch :: (Name,Term) -> TC (Name,Scoped Typ)
inferBranch (n,t) = (,) n <$> inferTerm t

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

inferTerm' :: Term -> TC Typ
inferTerm' = fmap unScoped . inferTerm

inferTerm :: Term -> TC (Scoped Typ)
inferTerm e0 = debug ["Inferring type of " ++ pretty e0] >> case e0 of
  Lit _           -> return $ emptyScope int
  TTyp            -> return sTyp -- type-in-type
  Def x es        -> inferDef x es
  Lam arg t       -> sFun arg <$> checkVarDec arg (inferTerm t)
  Con n           -> conType n
  Case t brs      -> join $ inferCase t <$> inferTerm t <*> mapM inferBranch brs
  Proc{}          -> throwError "inferTerm: NProc"
  TFun arg s      -> checkVarDec arg (checkTyp s) >> return sTyp
  TSig arg s      -> checkVarDec arg (checkTyp s) >> return sTyp
  TProto sessions -> checkSessions sessions       >> return sTyp

checkTerm :: Typ -> Term -> TC ()
checkTerm = checkTerm' . emptyScope

emptyScope :: a -> Scoped a
emptyScope = Scoped empty

checkTerm' :: Scoped Typ -> Term -> TC ()
checkTerm' expectedTyp e = do
  inferredTyp <- inferTerm e
  debug ["Checking term"
        ,"exp:      " ++ pretty e
        ,"expected: " ++ pretty expectedTyp
        ,"inferred: " ++ pretty inferredTyp
        ]
  checkTypeEquivalence expectedTyp inferredTyp

checkMaybeTerm :: Typ -> Maybe Term -> TC ()
checkMaybeTerm _   Nothing   = return ()
checkMaybeTerm typ (Just tm) = checkTerm typ tm

inferDef :: Name -> [Term] -> TC (Scoped Typ)
inferDef f es = do
  mtyp  <- view $ evars . at f
  defs  <- view edefs
  case mtyp of
    Just typ -> checkApp f (Scoped defs typ) es
    Nothing  -> throwError $ "unknown definition " ++ unName f

checkApp :: Name -> Scoped Typ -> [Term] -> TC (Scoped Typ)
checkApp _ typ []     = return typ
checkApp f typ (e:es) =
  case unDef typ of
    (Scoped defs typ'@(TFun (Arg x ty) s)) -> do
      checkTerm' (Scoped defs ty) e
      checkApp f (Ren.subst1 f (x, e) (Scoped defs s)) es
    _ -> throwError "checkApp: impossible"

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
