{-# LANGUAGE TemplateHaskell #-}
module Ling.Equiv (Equiv(equiv), EqEnv, emptyEqEnv, allEquiv) where

import           Control.Lens

import           Data.List            (elemIndex)
import           Data.Map             (Map)
import qualified Data.Map             as Map

import           Ling.Norm
import           Ling.Scoped          (Defs, Scoped (..), ldefs, scoped, unDef)
import           Ling.Utils           (Abs (..), Arg (..), Telescope (..))

data EqEnv = EqEnv
  { _eqnms  :: [(Name,Name)]
  , _edefs0
  , _edefs1 :: Defs
  }

$(makeLenses ''EqEnv)

emptyEqEnv :: Map Name Term -> EqEnv
emptyEqEnv x = EqEnv [] x x

-- TODO binders
-- Removing the definitions is wrong they might be needed by others
-- "Better" solution, use a different binder
ext :: EqEnv -> Name -> Name -> EqEnv
ext env x0 x1 = env & eqnms  %~ ((x0,x1):)
                    & edefs0 . at x0 .~ Nothing
                    & edefs1 . at x1 .~ Nothing

type IsEquiv a = EqEnv -> a -> a -> Bool

class Equiv a where
  equiv :: IsEquiv a

instance (Equiv a, Equiv b) => Equiv (Abs a b) where
  equiv env (Abs (Arg x0 s0) u0) (Abs (Arg x1 s1) u1) =
    equiv env s0 s1 && equiv (ext env x0 x1) u0 u1

instance (Equiv a, Equiv b) => Equiv (Telescope a b) where
  equiv env (Telescope args0 u0) (Telescope args1 u1) =
    case (args0, args1) of
      ([],       [])       -> equiv env u0 u1
      (a0 : as0, a1 : as1) -> equiv env (Abs a0 (Telescope as0 u0))
                                        (Abs a1 (Telescope as1 u1))
      _                    -> False

allEquiv :: Equiv a => EqEnv -> [a] -> Bool
allEquiv _   []         = False
allEquiv _   [_]        = True
allEquiv env (x0:x1:xs) = equiv env x0 x1 && allEquiv env (x0:xs)

instance (Equiv a, Equiv b) => Equiv (a, b) where
  equiv env (x0,y0) (x1,y1) = equiv env x0 x1 && equiv env y0 y1

instance Equiv a => Equiv [a] where
  equiv _   []       []       = True
  equiv env (x0:xs0) (x1:xs1) = equiv env x0 x1 && equiv env xs0 xs1
  equiv _   _        _        = False

instance Equiv a => Equiv (Maybe a) where
  equiv _   Nothing   Nothing   = True
  equiv env (Just x0) (Just x1) = equiv env x0 x1
  equiv _   _         _         = False

equivDef :: IsEquiv Term
equivDef env (Def x0 es0) (Def x1 es1) = equiv env (x0, es0) (x1, es1)
equivDef _   _            _            = False

nameIndex :: Name -> [Name] -> Either Int Name
nameIndex x = maybe (Right x) Left . elemIndex x

instance Equiv a => Equiv (Scoped a) where
  equiv env s0 s1 =
    equiv (env & edefs0 %~ Map.union (s0 ^. ldefs)
               & edefs1 %~ Map.union (s1 ^. ldefs))
          (s0 ^. scoped) (s1 ^. scoped)

instance Equiv Name where
  equiv env x0 x1 = i0 == i1
    where
      i0 = nameIndex x0 $ map fst es
      i1 = nameIndex x1 $ map snd es
      es = env ^. eqnms

instance Equiv Term where
  equiv env t0 t1 =
    t0 == t1 || -- Quadratic but safe
    equivDef env t0 t1 ||
    case (s0'^.scoped,s1'^.scoped) of
      (Def x0 es0,   Def x1 es1)   -> equiv env' (x0, es0) (x1, es1)
      (Lit l0,       Lit l1)       -> l0 == l1
      (Con c0,       Con c1)       -> c0 == c1
      (Case u0 brs0, Case u1 brs1) -> equiv env' (u0,brs0) (u1,brs1)
      (TTyp,         TTyp)         -> True
      (Lam  arg0 u0, Lam  arg1 u1) -> equiv env' (Abs arg0 u0) (Abs arg1 u1)
      (TFun arg0 u0, TFun arg1 u1) -> equiv env' (Abs arg0 u0) (Abs arg1 u1)
      (TSig arg0 u0, TSig arg1 u1) -> equiv env' (Abs arg0 u0) (Abs arg1 u1)
      (Proc cds0 p0, Proc cds1 p1) -> equiv env' (Telescope cds0 p0) (Telescope cds1 p1)
      (TProto ss0,   TProto ss1)   -> equiv env' ss0 ss1

      (Def{},        _)            -> False
      (Lit{},        _)            -> False
      (Con{},        _)            -> False
      (Case{},       _)            -> False
      (TTyp,         _)            -> False
      (Lam{},        _)            -> False
      (TFun{},       _)            -> False
      (TSig{},       _)            -> False
      (Proc{},       _)            -> False
      (TProto{},     _)            -> False
    where
      defs0 = env ^. edefs0
      defs1 = env ^. edefs1
      s0    = Scoped defs0 t0
      s1    = Scoped defs1 t1
      s0'   = unDef s0
      s1'   = unDef s1
      env'  = env & edefs0 .~ (s0'^.ldefs)
                  & edefs1 .~ (s1'^.ldefs)

instance Equiv RW where
  equiv _ Read  Read  = True
  equiv _ Write Write = True
  equiv _ _     _     = False

instance Equiv RSession where
  equiv env (s0 `Repl` t0) (s1 `Repl` t1) = equiv env (s0, t0) (s1, t1)

instance Equiv Session where
  equiv env s0' s1' =
    case (s0', s1') of
      (Atm rw0 n0, Atm rw1 n1) -> equiv env (rw0, n0) (rw1, n1)
      (End,        End)        -> True
      (Snd ty0 s0, Snd ty1 s1) -> equiv env (ty0, s0) (ty1, s1)
      (Rcv ty0 s0, Rcv ty1 s1) -> equiv env (ty0, s0) (ty1, s1)
      (Par ss0,    Par ss1)    -> equiv env ss0 ss1
      (Ten ss0,    Ten ss1)    -> equiv env ss0 ss1
      (Seq ss0,    Seq ss1)    -> equiv env ss0 ss1

      (Atm{}, _) -> False
      (End{}, _) -> False
      (Snd{}, _) -> False
      (Rcv{}, _) -> False
      (Par{}, _) -> False
      (Ten{}, _) -> False
      (Seq{}, _) -> False

instance Equiv Proc where
  equiv _ = (==)
  -- TODO
  -- equiv env (pref0 `Act` procs0) (pref1 `Act` procs1) =
