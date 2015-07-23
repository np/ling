{-# LANGUAGE TemplateHaskell #-}
-- , GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses #-}
module Ling.Equiv (Equiv(equiv), EqEnv, emptyEqEnv) where

import Control.Lens

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (findIndex)

import Ling.Abs (Name)
import Ling.Utils (Arg(Arg))
import Ling.Norm
import Ling.Subst

data EqEnv = EqEnv
  { _eqnms  :: [(Name,Name)]
  , _edefs0
  , _edefs1 :: Map Name Term
  }

$(makeLenses ''EqEnv)

emptyEqEnv :: Map Name Term -> EqEnv
emptyEqEnv x = EqEnv [] x x

ext :: EqEnv -> Name -> Name -> EqEnv
ext env x0 x1 = env & eqnms  %~ ((x0,x1):)
                    & edefs0 %~ Map.delete x0
                    & edefs1 %~ Map.delete x1

class Equiv a where
  equiv :: EqEnv -> a -> a -> Bool

equivBnd :: Equiv a => EqEnv -> Arg a -> a -> Arg a -> a -> Bool
equivBnd env (Arg x0 s0) u0 (Arg x1 s1) u1 = equiv env s0 s1 && equiv (ext env x0 x1) u0 u1

instance (Equiv a, Equiv b) => Equiv (a, b) where
  equiv env (x0,y0) (x1,y1) = equiv env x0 x1 && equiv env y0 y1

instance Equiv a => Equiv [a] where
  equiv _   []       []       = True
  equiv env (x0:xs0) (x1:xs1) = equiv env x0 x1 && equiv env xs0 xs1
  equiv _   _        _        = False

equivDef :: EqEnv -> Term -> Term -> Bool
equivDef env (Def x0 es0) (Def x1 es1) = equiv env (x0, es0) (x1, es1)
equivDef _   _            _            = False

nameIndex :: Name -> [Name] -> Either Int Name
nameIndex x = maybe (Right x) Left . findIndex (== x)

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
    case (t0',t1') of
      (Def x0 es0,   Def x1 es1)   -> equiv env (x0, es0) (x1, es1)
      (Lit l0,       Lit l1)       -> l0 == l1
      (TTyp,         TTyp)         -> True
      (Lam  arg0 u0, Lam  arg1 u1) -> equivBnd env arg0 u0 arg1 u1
      (TFun arg0 s0, TFun arg1 s1) -> equivBnd env arg0 s0 arg1 s1
      (TSig arg0 s0, TSig arg1 s1) -> equivBnd env arg0 s0 arg1 s1
      (Proc cds0 p0, Proc cds1 p1) -> error "Equiv Term: Proc: TODO"
      (TProto ss0,   TProto ss1)   -> equiv env ss0 ss1

      (Def{},        _)            -> False
      (Lit{},        _)            -> False
      (TTyp,         _)            -> False
      (Lam{},        _)            -> False
      (TFun{},       _)            -> False
      (TSig{},       _)            -> False
      (Proc{},       _)            -> False
      (TProto{},     _)            -> False
    where
      defs0 = env ^. edefs0
      defs1 = env ^. edefs1
      t0'   = unDef defs0 t0
      t1'   = unDef defs1 t1

instance Equiv RSession where
  equiv _ _ _ = error "Equiv Session: TODO"
