{-# LANGUAGE TemplateHaskell #-}
module Ling.Equiv (Equiv(equiv), EqEnv, emptyEqEnv, allEquiv) where

import           Control.Lens

import           Data.List            (elemIndex)
import           Data.Map             (Map)
import qualified Data.Map             as Map

import           Ling.Abs             (Name)
import           Ling.Norm
import           Ling.Print.Instances ()
import           Ling.Scoped          (Defs, Scoped (Scoped), ldefs, scoped,
                                       unDef)
import           Ling.Utils           (Arg (Arg))

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

class Equiv a where
  equiv :: EqEnv -> a -> a -> Bool

-- TODO (Ok1)
equivBnd :: Equiv a => EqEnv -> Arg a -> a -> Arg a -> a -> Bool
equivBnd env (Arg x0 s0) u0 (Arg x1 s1) u1 = equiv env s0 s1 && equiv (ext env x0 x1) u0 u1

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

equivDef :: EqEnv -> Term -> Term -> Bool
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
      (Lam  arg0 u0, Lam  arg1 u1) -> equivBnd env' arg0 u0 arg1 u1
      (TFun arg0 u0, TFun arg1 u1) -> equivBnd env' arg0 u0 arg1 u1
      (TSig arg0 u0, TSig arg1 u1) -> equivBnd env' arg0 u0 arg1 u1
      (Proc _cds0 _p0, Proc _cds1 _p1) -> error "Equiv Term: Proc: TODO"
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

instance Equiv RSession where
  equiv _ _ _ = error "Equiv Session: TODO"
