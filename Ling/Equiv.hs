{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
module Ling.Equiv (Equiv(equiv), EqEnv, emptyEqEnv, swapEnv) where

import           Ling.Norm
import           Ling.Prelude
import           Ling.Print
import           Ling.Reduce
import           Ling.Scoped

data EqEnv = EqEnv
  { _eqnms  :: [(Name,Name)]
  , _edefs0
  , _edefs1 :: Defs
  }

$(makeLenses ''EqEnv)

emptyEqEnv :: Map Name Term -> EqEnv
emptyEqEnv x = EqEnv [] x x

swapEnv :: Endom EqEnv
swapEnv (EqEnv nms ds0 ds1) = EqEnv (map swap nms) ds1 ds0

ext :: EqEnv -> Name -> Name -> EqEnv
ext env x0 x1
  | env^.edefs0.hasKey x0 =
      error $ "Name conflict: " ++ pretty x0 ++ " is already bound"
  | env^.edefs1.hasKey x1 =
      error $ "Name conflict: " ++ pretty x1 ++ " is already bound"
  | otherwise =
      env & eqnms %~ ((x0,x1):)
{-
-- NOTE: Removing the definitions as here would be wrong
-- since these definitions might be needed by others
-- "Better" solution, use a different binder
ext env x0 x1 = env & eqnms  %~ ((x0,x1):)
                    & edefs0 . at x0 .~ Nothing
                    & edefs1 . at x1 .~ Nothing
-}

type IsEquiv a = EqEnv -> Rel a

class Equiv a where
  equiv :: IsEquiv a

equivAt :: Equiv a => Getter s a -> IsEquiv s
equivAt f env x y = equiv env (x^.f) (y^.f)

reduceEquiv :: (Print a, Print b) =>
               (Scoped a -> Scoped b) -> IsEquiv b -> IsEquiv a
reduceEquiv red eqv env a0 a1 = eqv env' (a0'^.scoped) (a1'^.scoped)
  where
    red' l = red . Scoped (env^.l)
    a0'    = red' edefs0 a0
    a1'    = red' edefs1 a1
    env'  = env & edefs0 %~ mergeDefs (a0'^.ldefs)
                & edefs1 %~ mergeDefs (a1'^.ldefs)

-- This type can be used on type or sessions annotations to ignore them during
-- equivalence checking.
-- Equivalence checking is defined for terms of a common type.
-- Therefore we do not check for the equivalence of the type annotations on
-- constructions such as `Lam`, `Proc`.
-- However annotians on `TFun`, `TSig` matters.
newtype Ignored a = Ignored a
  deriving (Eq, Ord, Read, Show)

instance Equiv (Ignored a) where
  equiv _ Ignored{} Ignored{} = True

ignoreArgBody :: Arg a -> Arg (Ignored a)
ignoreArgBody = argBody %~ Ignored

-- NOTE that Typ are ignored here.
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
    equivAt scoped
          (env & edefs0 %~ mergeDefs (s0 ^. ldefs)
               & edefs1 %~ mergeDefs (s1 ^. ldefs))
          s0 s1

instance Equiv Name where
  equiv env x0 x1 = i0 == i1
    where
      i0 = nameIndex x0 $ fst <$> es
      i1 = nameIndex x1 $ snd <$> es
      es = env ^. eqnms

instance Equiv Term where
  equiv env t0 t1 = equivDef env t0 t1 || reduceEquiv reduceWHNF equivRedTerm env t0 t1

equivRedTerm :: IsEquiv Term
equivRedTerm env s0 s1 =
    case (s0,s1) of
      (Def x0 es0,   Def x1 es1)   -> equiv env (x0, es0) (x1, es1)
      (Lit l0,       Lit l1)       -> l0 == l1
      (Con c0,       Con c1)       -> c0 == c1
      (Case u0 brs0, Case u1 brs1) -> equiv env (u0,brs0) (u1,brs1)
      (TTyp,         TTyp)         -> True
      (Lam  arg0 u0, Lam  arg1 u1) -> equiv env (Abs (ignoreArgBody arg0) u0)
                                                (Abs (ignoreArgBody arg1) u1)
      (TFun arg0 u0, TFun arg1 u1) -> equiv env (Abs arg0 u0) (Abs arg1 u1)
      (TSig arg0 u0, TSig arg1 u1) -> equiv env (Abs arg0 u0) (Abs arg1 u1)
      (Proc cds0 p0, Proc cds1 p1) -> equiv env (Telescope (ignoreArgBody<$>cds0) p0)
                                                (Telescope (ignoreArgBody<$>cds1) p1)
      (TProto ss0,   TProto ss1)   -> equiv env (RS ss0) (RS ss1)
      (TSession se0, TSession se1) -> case (se0, se1) of
        (IO p0 ty0 se0', IO p1 ty1 se1') -> equiv env (p0, Abs ty0 se0') (p1, Abs ty1 se1')
        (Array k0 ss0,   Array k1 ss1)   -> equiv env (k0, RS ss0) (k1, RS ss1)

        -- The normal form should prevent u0/u1 to be TSession (TermS _ _)
        -- themselves. Otherwise we would miss equivalences such as ~~A === A.
        (TermS op0 u0,   TermS op1 u1)   -> equiv env (op0, u0) (op1, u1)

        (IO{}, _)    -> False
        (Array{}, _) -> False
        (TermS{}, _) -> False

      (Let defs0 t0, Let defs1 t1) -> equiv env (Scoped defs0 t0) (Scoped defs1 t1)
      (Let defs0 t0, _)            -> equiv env (Scoped defs0 t0) (pure s1)
      (_,            Let defs1 t1) -> equiv env (pure s0)         (Scoped defs1 t1)

      (Def{},        _) -> False
      (Lit{},        _) -> False
      (Con{},        _) -> False
      (Case{},       _) -> False
      (TTyp,         _) -> False
      (Lam{},        _) -> False
      (TFun{},       _) -> False
      (TSig{},       _) -> False
      (Proc{},       _) -> False
      (TProto{},     _) -> False
      (TSession{},   _) -> False

instance Equiv RW where
  equiv _ = (==)

instance Equiv DualOp where
  equiv _ = (==)

instance Equiv TraverseKind where
  equiv _ = (==)

instance Equiv RSession where
  equiv env (s0 `Repl` r0) (s1 `Repl` r1) = equiv env (s0, r0) (s1, r1)

newtype RSessions = RS [RSession]

instance Equiv RSessions where
  equiv env (RS srs0) (RS srs1) = reduceEquiv flatSessions equiv env srs0 srs1

instance Equiv RFactor where
  equiv env (RFactor t0) (RFactor t1) = equiv env t0 t1

instance Equiv Session where
  equiv = equivAt tSession

-- NOTE that type and session annotations are ignored as in the `Abs` instance.
instance Equiv Act where
  equiv env a0 a1 = case (a0 , a1) of
    (Recv c0 _b0, Recv c1 _b1) -> c0 == c1
    (Send c0 t0, Send c1 t1) -> c0 == c1 && equiv env t0 t1
    (At t0 p0, At t1 p1) -> equiv env t0 t1 && p0 == p1
    (Nu cd0 cd0', Nu cd1 cd1') ->
       on (==) (both %~ _argName) (cd0, cd0') (cd1, cd1')
    (Split k0 c0 cds0, Split k1 c1 cds1) ->
       (k0, c0) == (k1, c1) && on (==) (_argName <$>) cds0 cds1
    (NewSlice cs0 r0 _x0, NewSlice cs1 r1 _x1) ->
       cs0 == cs1 && equiv env r0 r1
    (Ax _s0 cs0, Ax _s1 cs1) ->
       cs0 == cs1
    (Recv{} , _) -> False
    (Send{} , _) -> False
    (At{} , _) -> False
    (Nu{} , _) -> False
    (Split{} , _) -> False
    (NewSlice{} , _) -> False
    (Ax{} , _) -> False

instance Equiv Proc where
  equiv env (pr0 `Dot` pp0) (pr1 `Dot` pp1) =
      equiv env (pr0, Telescope vd0 pp0) (pr1, Telescope vd1 pp1)
    where
      vd0 = ignoreArgBody <$> (actVarDecs =<< pr0)
      vd1 = ignoreArgBody <$> (actVarDecs =<< pr1)
