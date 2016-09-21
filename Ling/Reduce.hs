{-# LANGUAGE ConstraintKinds              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving   #-}
{-# LANGUAGE LambdaCase                   #-}
{-# LANGUAGE MultiParamTypeClasses        #-}
{-# LANGUAGE Rank2Types                   #-}
{-# LANGUAGE TemplateHaskell              #-}
module Ling.Reduce where

import           Ling.Fwd
import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Print
import           Ling.Proc
import           Ling.Rename
import           Ling.Scoped
import           Ling.Session.Core

-- This `strong` mode is not really useful. Ling.Subst is already
-- implementing the strong reductfuse semantics so Ling.Reduce
-- can be kept as the lazy/weak version.
strong :: Bool
strong = False

newtype Reduced a = Reduced { _reduced :: Scoped a }
  deriving (Eq, Show, Monoid, Functor, Applicative)

makePrisms ''Reduced
makeLenses ''Reduced

instance Print a => Print (Reduced a) where
  prt i = prt i . view reduced

type Reduce a b = Scoped a -> Reduced b
type Reduce' a = Reduce a a

class HasReduce a b where
  reduce :: Reduce a b

type HasReduce' a = HasReduce a a

traceReduce :: (Print a, Print b, Show a, Show b)
            => String -> Scoped a -> Reduced b -> Reduced b
traceReduce _ _ = id
--traceReduce msg x y = trace (msg ++ ":\n" ++ pretty (x ^. scoped)) (y `seq` trace ("---> " ++ pretty (y ^. reduced . scoped)) y)
--traceReduce msg x y = trace (msg ++ ":\n" ++ ppShow (x ^. scoped)) (y `seq` trace ("---> " ++ ppShow (y ^. reduced . scoped)) y)
--traceReduce msg x y = trace (msg ++ ":\n" ++ ppShow (x & gdefs .~ ø)) (y `seq` trace ("---> " ++ ppShow (y & reduced . gdefs .~ ø)) y)
--traceReduce msg x y = trace (msg ++ ":\n" ++ ppShow x) (y `seq` trace ("---> " ++ ppShow y) y)

alreadyReduced :: Scoped a -> Reduced a
alreadyReduced s = pure $ s ^. scoped

reducedOrReduce :: HasReduce' a => Scoped a -> Reduced a
reducedOrReduce
  | strong    = reduce
  | otherwise = alreadyReduced

reduceApp :: Scoped Term -> [Term] -> Reduced Term
reduceApp st0 = \case
  []     -> Reduced (st0 & gdefs .~ ø) *> rt1
  (u:us) ->
    traceReduce "reduceApp" st1 $
    case st1 ^. scoped of
      Lam (Arg x mty) t2 -> reduceApp (st0 *> st1 *> subst1 (x, Ann mty u) t2) us
      Def k d es -> reduceDef (st0 *> st1 $> (k, d, es ++ u : us))
      _ -> error "Ling.Reduce.reduceApp: IMPOSSIBLE"

  where
    rt1 = reduce st0
    st1 = rt1 ^. reduced
    -- st1 might have less (or even no) defs than st0.

reduceCase :: Scoped Term -> [Branch] -> Reduced Term
reduceCase st0 brs =
  traceReduce "reduceCase" st0 $
  case st1 ^. reduced . scoped of
    Con con
      | Just rhs <- lookup con brs -> reduce (st0 $> rhs)
      | otherwise                  -> error "reduceCase: IMPOSSIBLE"
    _ | strong    -> mkCase <$> st1 <*> reduce (st0 $> brs)
      | otherwise -> (`Case` brs) <$> st1
                  -- ^ no need for mkCase here since:
                  -- * the scrutinee is not a constructor
                  -- * the branches have not changed
                  -- * mkCase would not do anything useful
  where st1 = reduce st0

mkBool :: Bool -> Term
mkBool False = Con (Name "false")
mkBool True  = Con (Name "true")

-- The resulting Term should be in normal form.
reducePrim :: String -> [Literal] -> Maybe Term
reducePrim "_+_"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x + y
reducePrim "_-_"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x - y
reducePrim "_*_"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x * y
reducePrim "_/_"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x `div` y
reducePrim "_%_"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x `mod` y
reducePrim "pow"        [LInteger x, LInteger y] = Just . Lit . LInteger $ x ^ y
reducePrim "_+D_"       [LDouble  x, LDouble  y] = Just . Lit . LDouble  $ x + y
reducePrim "_-D_"       [LDouble  x, LDouble  y] = Just . Lit . LDouble  $ x - y
reducePrim "_*D_"       [LDouble  x, LDouble  y] = Just . Lit . LDouble  $ x * y
reducePrim "_/D_"       [LDouble  x, LDouble  y] = Just . Lit . LDouble  $ x / y
reducePrim "powD"       [LDouble  x, LDouble  y] = Just . Lit . LDouble  $ x ** y
reducePrim "_++S_"      [LString  x, LString  y] = Just . Lit . LString  $ x ++ y
reducePrim "Int2Double" [LInteger x]             = Just . Lit . LDouble  $ fromInteger x
reducePrim "showInt"    [LInteger x]             = Just . Lit . LString  $ show x
reducePrim "showDouble" [LDouble  x]             = Just . Lit . LString  $ show x
reducePrim "showChar"   [LChar    x]             = Just . Lit . LString  $ show x
reducePrim "showString" [LString  x]             = Just . Lit . LString  $ show x
reducePrim "_==I_"      [LInteger x, LInteger y] = Just . mkBool $ x == y
reducePrim "_==D_"      [LDouble  x, LDouble  y] = Just . mkBool $ x == y
reducePrim "_==C_"      [LChar    x, LChar    y] = Just . mkBool $ x == y
reducePrim "_==S_"      [LString  x, LString  y] = Just . mkBool $ x == y
reducePrim _            _                        = Nothing

reduceDef :: Scoped (DefKind, Name, [Term]) -> Reduced Term
reduceDef sdef =
  -- traceReduce "reduceDef" sdef $
  case sdef ^. scoped of
    (k, d, es) ->
      case k of
        Defined
          | Just st <- scopedName (sdef $> d) -> reduceApp st es
        Undefined
          | Just ls <- es' ^? reduced . scoped . below _Lit
          , Just  e <- reducePrim (unName # d) ls -> pure e
        _ -> Def k d <$> es'
      where
        es' = reduce (sdef $> es)

instance HasReduce a b => HasReduce (Maybe a) (Maybe b) where reduce = reduceEach
instance HasReduce a b => HasReduce [a] [b]             where reduce = reduceEach
instance HasReduce a b => HasReduce (Arg a) (Arg b)     where reduce = reduceEach

instance (HasReduce a b, HasReduce a' b') => HasReduce (a, a') (b, b') where
  reduce sxy = bitraverse (reduce . (sxy $>)) (reduce . (sxy $>)) (sxy ^. scoped)

-- Only needed for ConName
instance HasReduce Name Name where reduce = alreadyReduced

instance HasReduce Session Session where
  reduce s0 =
    case s0 ^. scoped of
      TermS p t1 -> (view (from tSession) . sessionOp p) <$> reduce (s0 $> t1)
      Array k ss -> whenStrong $ Array k <$> reduce (s0 $> ss)
      IO rw vd s -> whenStrong $ IO rw <$> reduce (s0 $> vd) <*> reduce (s0 $> s)
    where
      whenStrong s | strong    = s
                   | otherwise = alreadyReduced s0

instance HasReduce RFactor RFactor where
  reduce = reduce_ rterm

instance HasReduce RSession RSession where
  reduce rs0 =
    case rs0 ^. scoped of
      s `Repl` r -> Repl <$> reduce (rs0 $> s) <*> reduce (rs0 $> r)

instance HasReduce ChanDec ChanDec where
  reduce scd =
    case scd ^. scoped of
      ChanDec c r os -> ChanDec c <$> reduce (scd $> r) <*> reduce (scd $> os)

instance HasReduce Term Term where
  reduce st0 =
    -- traceReduce "reduceTerm" st0 $
    case t0 of
      Let defs t  -> Reduced (Scoped ø defs ()) *> reduce (st0 *> Scoped defs ø () $> t)
      Def k d es  -> reduceDef (st0 $> (k, d, es))
      Case t brs  -> reduceCase (st0 $> t) brs
      Lit{}       -> pure t0
      TTyp        -> pure t0
      Con{}       -> pure t0
      Proc cds p  -> whenStrong $ Proc <$> reduce (st0 $> cds) <*> reduce (st0 $> p)
      Lam  arg t  -> whenStrong $ Lam <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TFun arg t  -> whenStrong $ TFun <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TSig arg t  -> whenStrong $ TSig <$> reduce (st0 $> arg) <*> reduce (st0 $> t)
      TProto ss   -> whenStrong $ TProto <$> reduce (st0 $> ss)
      TSession s0 -> view tSession <$> reduce (st0 $> s0)

    where
      t0 = st0 ^. scoped
      whenStrong s | strong    = s
                   | otherwise = alreadyReduced st0

-- TODO assumptions!!!
reduce_ :: HasReduce a b => Traversal s t a b -> Reduce s t
reduce_ trv ss = trv (reduce . (ss $>)) (ss ^. scoped)

reduceEach :: (Each s t a b, HasReduce a b) => Reduce s t
reduceEach = reduce_ each

flatRSession :: Scoped RSession -> [Scoped RSession]
flatRSession ssr
  | Just n <- r1 ^? litR . integral = replicate n (pure $ oneS s)
  | Just (rL,rR) <- r1 ^? addR      = flatRSession (sr1 $> s `Repl` rL)
                                   ++ flatRSession (sr1 $> s `Repl` rR)
  | otherwise                       = [ssr]

  where sr1 = reduce_ rterm (ssr $> r0) ^. reduced
        s   = ssr ^. scoped . rsession
        r0  = ssr ^. scoped . rfactor
        r1  = sr1 ^. scoped

flatRSessions :: Scoped Sessions -> [Scoped RSession]
flatRSessions sss = sss ^. scoped . _Sessions >>= flatRSession . (sss $>)

instance HasReduce Sessions Sessions where
  reduce = Reduced . fmap Sessions . sequenceA . flatRSessions

-- Prism valid up to the reduction rules
_ActAt :: Prism' Proc (Term, CPatt)
_ActAt = prism con pat
  where
    con (t, p) =
      -- (\proc0 -> trace ("_ActAt (" ++ ppShow t ++ ", " ++ ppShow p ++ ") = " ++ ppShow proc0) proc0) $
      case t of
        Proc cs0 proc0 ->
          case cPattAsArrayChanDecs p of
            Just (k, cs') | Just (pref1, cs1, proc1) <- matchChanDecs k (id, cs0, proc0)
                          , length cs1 == length cs' -> pref1 $ renProc (zip cs1 cs') proc1
                          | k == ParK
                          , length cs0 == length cs' -> renProc (zip cs0 cs') proc0
            _ -> p0
        _ -> p0
      where
        p0 = Act (At t p)

    pat (Act (At t p)) = Right (t, p)
    pat proc0          = Left  proc0

    renProc bs = renameI r
      where
        l = bs & each . both %~ view cdChan
        m = l2m l
        r = Ren (\_ _ x -> pure $ m ^. at x ?| x) ø ø

-- Prism valid up to the reduction rules
__Act :: Prism' Proc Act
__Act = prism con pat
  where
    con act = Act act & _ActAt %~ id
                      & expandFwd
    pat (Act act) = Right act
    pat proc0     = Left proc0

-- This is not really about some sort of Weak Head Normal Form.
-- What matters is:
-- * To reduce the At constructor:
--     @(proc(Γ) P){Γ} -> P
-- * Push LetP
instance HasReduce Proc Proc where
  reduce sp =
    case sp ^. scoped of
      Act act -> reduce_ (_ActAt . _1) (sp $> Act act)
      proc0 `Dot` proc1 -> (dotP :: Op2 Proc) <$> reduce (sp $> proc0) <*> reduce (sp $> proc1)
      LetP defs proc0 ->
        reduce (sp *> Scoped defs ø () $> proc0) & reduced . scoped %~ LetP defs
      Replicate k r n p ->
        mkReplicate k <$> reducedOrReduce (sp $> r) <*> pure n <*> reduce (sp $> p)
      Procs procs -> procs ^. each . to (reduce . (sp $>))
