{-# LANGUAGE TemplateHaskell #-}
module Ling.Equiv (Equiv(equiv), EqEnv, emptyEqEnv) where

import qualified Data.Map             as Map

import           Ling.Norm
import           Ling.Reduce          (reduceWHNF)
import           Ling.Scoped          (Defs, Scoped (..), ldefs, scoped)
import           Ling.Prelude

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

instance (Equiv a, Equiv b) => Equiv (a, b) where
  equiv env (x0,y0) (x1,y1) = equiv env x0 x1 && equiv env y0 y1

instance Equiv a => Equiv [a] where
  equiv _   []       []       = True
  equiv env (x0:xs0) (x1:xs1) = equiv env (x0, xs0) (x1, xs1)
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
      i0 = nameIndex x0 $ fst <$> es
      i1 = nameIndex x1 $ snd <$> es
      es = env ^. eqnms

instance Equiv Term where
  equiv env t0 t1 =
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
      (TSession se0, TSession se1) -> case (se0, se1) of
        (IO p0 ty0 se0', IO p1 ty1 se1') -> equiv env' (p0, Abs ty0 se0') (p1, Abs ty1 se1')
        (Array k0 ss0,   Array k1 ss1)   -> equiv env' (k0, ss0) (k1, ss1)

        -- The normal form should prevent u0/u1 to be TSession (TermS _ _)
        -- themselves. Otherwise we would miss equivalences such as ~~A === A.
        (TermS op0 u0,   TermS op1 u1)   -> equiv env' (op0, u0) (op1, u1)

        (IO{}, _)    -> False
        (Array{}, _) -> False
        (TermS{}, _) -> False

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
      (TSession{},   _)            -> False
    where
      defs0 = env ^. edefs0
      defs1 = env ^. edefs1
      s0    = Scoped defs0 t0
      s1    = Scoped defs1 t1
      s0'   = reduceWHNF s0
      s1'   = reduceWHNF s1
      env'  = env & edefs0 .~ (s0'^.ldefs)
                  & edefs1 .~ (s1'^.ldefs)

instance Equiv RW where
  equiv _ = (==)

instance Equiv DualOp where
  equiv _ = (==)

instance Equiv TraverseKind where
  equiv _ = (==)

instance Equiv RSession where
  equiv env (s0 `Repl` t0) (s1 `Repl` t1) = equiv env (s0, t0) (s1, t1)

instance Equiv Session where
  equiv env s0' s1' = equiv env (tSession s0') (tSession s1')

instance Equiv Act where
  equiv env a0 a1 = case (a0 , a1) of
    (Recv c0 b0, Recv c1 b1) -> c0 == c1
      && equiv env (b0 ^. unArg) (b1 ^. unArg)
    (Send c0 t0, Send c1 t1) -> c0 == c1 && equiv env t0 t1
    -- TODO: Add for splicing and At
    (_ , _) -> a0 == a1

instance Equiv Proc where
  equiv env (pr0 `Dot` pp0) (pr1 `Dot` pp1) =
      equiv env (pr0, Telescope cd0 pp0) (pr1, Telescope cd1 pp1)
    where
      cd0 = actVarDecs =<< pr0
      cd1 = actVarDecs =<< pr1
