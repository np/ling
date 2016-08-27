{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}

{-
This module implements hereditary substitution and also the following
reduction rules:
* prim ops
* case
* @(proc...)
-}
module Ling.Subst (Subst(subst), substScoped) where

import           Ling.Norm
import           Ling.Prelude hiding (subst1)
import           Ling.Proc
import           Ling.Reduce (reducePrim)
import           Ling.Rename (boundVars)
import           Ling.Scoped
import           Ling.Session

class Subst a where
  subst :: Defs -> Endom a

substApp :: Defs -> Term -> [Term] -> Term
substApp f e0 []     = subst f e0
substApp f e0 (e:es) =
  case e0 of
    Lam (Arg x mty) t1 ->
      substApp f (substScoped (subst1 (x, Ann mty (subst f e)) t1)) es

    Def d es0          -> substDef f d (es0 ++ e : es)
    _                  -> error "Ling.Subst.app: IMPOSSIBLE"

substDef :: Defs -> Name -> [Term] -> Term
substDef f d es
  | Just e <- f ^? at d . _Just . annotated = substApp f e es
  | "_:_" <- unName # d, [_,e] <- es      = subst f e
  | Just ls <- es' ^? below _Lit
  , Just  l <- reducePrim (unName # d) ls = Lit l
  | otherwise                             = Def d (subst f es)

  where
    es' = subst f es

substScoped :: Subst a => Scoped a -> a
substScoped s = subst (allDefs s) (s ^. scoped)

-- TODO binder: make an instance for Abs and use it for Lam,TFun,TSig

instance Subst Term where
  subst f = \case
    Def d es   -> substDef f d es
    Let defs t -> subst (subst f defs <> f) t
    Lam arg t  -> Lam (subst f arg) (subst (hide argName arg f) t)
    TFun arg t -> TFun (subst f arg) (subst (hide argName arg f) t)
    TSig arg t -> TSig (subst f arg) (subst (hide argName arg f) t)
    Case t brs -> mkCase (subst f t) (second (subst f) <$> brs)
    e0@Con{}   -> e0
    e0@TTyp    -> e0
    e0@Lit{}   -> e0
    Proc cs p  -> Proc (subst f cs) (subst f p)
    TProto rs  -> TProto (subst f rs)
    TSession s -> subst f s ^. tSession

instance Subst Defs where
  subst = over each . subst

instance (Subst a, Subst b) => Subst (Ann a b) where
  subst f = bimap (subst f) (subst f)

instance Subst a => Subst (Arg a) where
  subst f (Arg x e) = Arg x (subst f e)

instance Subst a => Subst [a] where
  subst = map . subst

instance Subst a => Subst (Prll a) where
  subst = over unPrll . subst

instance Subst a => Subst (Maybe a) where
  subst = fmap . subst

instance (Subst a, Subst b) => Subst (a, b) where
  subst f = bimap (subst f) (subst f)

hide :: Fold s Name -> s -> Endom Defs
hide f = composeMapOf f sans

instance Subst NewPatt where
  subst f = \case
    NewChans k cs -> NewChans k (subst f cs)
    NewChan c os  -> NewChan c (subst f os)

instance Subst Act where
  subst f = \case
    Split c pat  -> Split c (subst f pat)
    Send c os e  -> Send c (subst f os) (subst f e)
    Recv c arg   -> Recv c (subst f arg)
    Nu ann npatt -> Nu (subst f ann) (subst f npatt)
    LetA{}       -> LetA ø
    Ax s cs      -> Ax (subst f s) cs
    At t cs      -> At (subst f t) (subst f cs)

instance Subst ChanDec where
  subst f (ChanDec c r os) = ChanDec c (subst f r) (subst f os)

instance Subst CPatt where
  subst f = \case
    ChanP cd    -> ChanP (subst f cd)
    ArrayP k ps -> ArrayP k (subst f ps)

instance Subst Proc where
  subst f = \case
    Act act -> __Act # subst f act
    proc0 `Dot` proc1 ->
      subst f proc0 `Dot` subst f1 proc1
      where
        defs0 = proc0 ^. procActs . actDefs
        f1 = hide boundVars proc0 f <> subst f defs0
    Procs procs -> Procs $ subst f procs
    NewSlice cs t x p -> NewSlice cs (subst f t) x (subst (hide id x f) p)

instance Subst Session where
  subst f = \case
    Array k ss -> Array k (subst f ss)
    IO p arg s -> IO p (subst f arg) (subst (hide argName arg f) s)
    TermS p t  -> termS p (subst f t)

instance Subst RSession where
  subst f (Repl s t) = Repl (subst f s) (subst f t)

instance Subst Sessions where
  subst = over _Sessions . subst

instance Subst RFactor where
  subst = over _RFactor . subst
