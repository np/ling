{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
module Ling.Equiv (Equiv(equiv), EqEnv, eqEnv, swapEnv) where

import           Ling.Norm
import           Ling.Prelude
import           Ling.Proc (_Pref)
import           Ling.Print
import           Ling.Reduce
import           Ling.Scoped

data EqEnv = EqEnv
  { _eqnms  :: [(Name,Name)]
  , _edefs0
  , _edefs1
  , _egdefs :: Defs
  }
  deriving Show

makeLenses ''EqEnv

scope :: Getting Defs EqEnv Defs -> a -> Getter EqEnv (Scoped a)
scope l x = to $ \env -> Scoped (env^.egdefs) (env^.l) x

eqEnv :: MonadReader s m => Lens' s Defs -> m EqEnv
eqEnv l = views l (EqEnv [] ø ø)

swapEnv :: Endom EqEnv
swapEnv e =
  EqEnv { _eqnms  = map swap (e ^. eqnms)
        , _edefs0 = e ^. edefs1
        , _edefs1 = e ^. edefs0
        , _egdefs = e ^. egdefs
        }

ext :: Name -> Name -> Endom EqEnv
ext x0 x1 env
  -- If any of the bound name is anon then
 -- | x0 == anonName || x1 == anonName = env
  | env^.egdefs.hasKey x0 =
      error $ "Name conflict: " ++ pretty x0 ++ " is already bound"
  | env^.egdefs.hasKey x1 =
      error $ "Name conflict: " ++ pretty x1 ++ " is already bound"
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
ext x0 x1 env = env & eqnms  %~ ((x0,x1):)
                    & edefs0 . at x0 .~ Nothing
                    & edefs1 . at x1 .~ Nothing
-}

type IsEquiv a = EqEnv -> Rel a

class Equiv a where
  equiv :: IsEquiv a

traceEquiv :: (Print a, Show a, {-Print r,-} Show r)
            => String -> EqEnv -> a -> a -> Endom r
traceEquiv _ _ _ _ = id
--traceEquiv msg env x y = trace (msg ++ ":\n" ++ pretty (env, x, y))
--traceEquiv msg env x y r = trace (msg ++ ":\n" ++ ppShow (env, x, y, r)) r

equivAt :: Equiv a => Getter s a -> IsEquiv s
equivAt f env x y = equiv env (x^.f) (y^.f)

reduceEquiv :: (Print a, Print reduced) =>
               Reduce a reduced -> IsEquiv reduced -> IsEquiv a
reduceEquiv red eqv env a0 a1 = eqv env' (a0'^.scoped) (a1'^.scoped)
  where
    red' l = view reduced . red . (env ^.) . scope l
    a0'    = red' edefs0 a0
    a1'    = red' edefs1 a1
    env'  = env & edefs0 <>~ a0' ^. ldefs
                & edefs1 <>~ a1' ^. ldefs

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

instance (Equiv a, Equiv b) => Equiv (Abs a b) where
  equiv env (Abs (Arg x0 s0) u0) (Abs (Arg x1 s1) u1) =
    equiv env s0 s1 && equiv (ext x0 x1 env) u0 u1

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

nameIndex :: Name -> [Name] -> Either Int Name
nameIndex x = maybe (Right x) Left . elemIndex x

instance Equiv a => Equiv (Scoped a) where
  equiv env s0 s1 =
    equivAt scoped
          (env & edefs0 <>~ s0 ^. ldefs
               & edefs1 <>~ s1 ^. ldefs)
          s0 s1

instance Equiv Name where
  equiv env x0 x1 = i0 == i1
    where
      i0 = nameIndex x0 $ fst <$> es
      i1 = nameIndex x1 $ snd <$> es
      es = env ^. eqnms

instance Equiv Term where
  equiv env t0 t1 =
    traceEquiv "Equiv Term" env t0 t1 $
    case (t0, t1) of
      (Def _k0 d0 es0, Def _k1 d1 es1)
        {-
        -- Undefined names could be primitive functions so this might miss these.
        | Undefined <- k0, Undefined <- k1, d0 == d1 -> equiv env es0 es1
        | Defined   <- k0, Defined   <- k1, equiv env (d0, es0) (d1, es1) -> True
        -}
        | equiv env (d0, es0) (d1, es1) -> True
      _ -> reduceEquiv reduce equivRedTerm env t0 t1

-- The session annotation is ignored
chanDecArg :: ChanDec -> Arg RFactor
chanDecArg (ChanDec c r _) = Arg c r

equivRedTerm :: IsEquiv Term
equivRedTerm env s0 s1 =
    traceEquiv "Equiv Reduced Term" env s0 s1 $
    case (s0,s1) of
      (Def _ d0 es0, Def _ d1 es1) -> equiv env (d0, es0) (d1, es1)
      (Lit l0,       Lit l1)       -> l0 == l1
      (Con c0,       Con c1)       -> c0 == c1
      (Case u0 brs0, Case u1 brs1) -> equiv env (u0,brs0) (u1,brs1)
      (TTyp,         TTyp)         -> True
      (Lam  arg0 u0, Lam  arg1 u1) -> equiv env (Abs (ignoreArgBody arg0) u0)
                                                (Abs (ignoreArgBody arg1) u1)
      (TFun arg0 u0, TFun arg1 u1) -> equiv env (Abs arg0 u0) (Abs arg1 u1)
      (TSig arg0 u0, TSig arg1 u1) -> equiv env (Abs arg0 u0) (Abs arg1 u1)
      (Proc cds0 p0, Proc cds1 p1) -> equiv env (Telescope (chanDecArg<$>cds0) p0)
                                                (Telescope (chanDecArg<$>cds1) p1)
      (TProto ss0,   TProto ss1)   -> equiv env ss0 ss1
      (TSession se0, TSession se1) -> case (se0, se1) of
        (IO p0 ty0 se0', IO p1 ty1 se1') -> equiv env (p0, Abs ty0 se0') (p1, Abs ty1 se1')
        (Array k0 ss0,   Array k1 ss1)   -> equiv env (k0, ss0) (k1, ss1)

        -- The normal form should prevent u0/u1 to be TSession (TermS _ _)
        -- themselves. Otherwise we would miss equivalences such as ~~A === A.
        (TermS op0 u0,   TermS op1 u1)   -> equiv env (op0, u0) (op1, u1)

        (IO{}, _)    -> False
        (Array{}, _) -> False
        (TermS{}, _) -> False

      (Let defs0 t0, Let defs1 t1) -> warn $ equiv env (Scoped ø defs0 t0) (Scoped ø defs1 t1)
      (Let defs0 t0, _)            -> warn $ equiv env (Scoped ø defs0 t0) (pure s1)
      (_,            Let defs1 t1) -> warn $ equiv env (pure s0)           (Scoped ø defs1 t1)

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
    where
      warn = trace "[WARNING] equivRedTerm should compare normal forms and `let` is not in normal form."

instance Equiv RW where
  equiv _ = (==)

instance Equiv SessionOp where
  equiv _ = (==)

instance Equiv TraverseKind where
  equiv _ = (==)

instance Equiv RSession where
  equiv env (s0 `Repl` r0) (s1 `Repl` r1) = equiv env (s0, r0) (s1, r1)

instance Equiv Sessions where
  equiv = reduceEquiv reduce (equivAt _Sessions)

instance Equiv RFactor where
  equiv = equivAt _RFactor

instance Equiv Session where
  equiv = equivAt tSession

instance Equiv NewPatt where
  equiv env np0 np1 = case (np0, np1) of
    (NewChans k0 cds0, NewChans k1 cds1) ->
      k0 == k1 &&
      -- Annotations are ignored as they are semantic preserving
      on (==)        (each %~ _cdChan) cds0 cds1 &&
      on (equiv env) (each %~ _cdRepl) cds0 cds1
    (NewChan c0 _os0, NewChan c1 _os1) ->
      -- Type annotations are ignored as they are semantic preserving
      c0 == c1
    (NewChans{}, _) -> False
    (NewChan{}, _) -> False

instance Equiv CPatt where
  equiv env pat0 pat1 = case (pat0, pat1) of
    (ChanP cd0, ChanP cd1) ->
      ((==) `on` _cdChan) cd0 cd1 &&
      ((equiv env) `on` _cdRepl) cd0 cd1
    (ArrayP k0 pats0, ArrayP k1 pats1) ->
       k0 == k1 && equiv env pats0 pats1
    (ChanP{}, _) -> False
    (ArrayP{}, _) -> False

-- NOTE that type and session annotations are ignored as in the `Abs` instance.
instance Equiv Act where
  equiv env a0 a1 = case (a0 , a1) of
    (Recv c0 _b0, Recv c1 _b1)             -> c0 == c1
    (Send c0 _os0 t0, Send c1 _os1 t1)     -> c0 == c1 && equiv env t0 t1
    (At t0 p0, At t1 p1)                   -> equiv env (t0, p0) (t1, p1)
    (Nu _ann0 newpatt0, Nu _ann1 newpatt1) -> equiv env newpatt0 newpatt1
    (Split c0 pat0, Split c1 pat1)         -> c0 == c1 && equiv env pat0 pat1
    (Ax _s0 cs0, Ax _s1 cs1)               -> cs0 == cs1

    (Recv{} , _) -> False
    (Send{} , _) -> False
    (At{} , _) -> False
    (Nu{} , _) -> False
    (Split{} , _) -> False
    (Ax{} , _) -> False

-- TODO: a bare minimum would be to sort the sub terms according to
-- something invariant under reduction, namely: free channels
instance Equiv a => Equiv (Prll a) where
  equiv env (Prll xs0) (Prll xs1) =
    equiv env xs0 xs1

instance Equiv Proc where
  equiv env (Act act0) (Act act1) =
    equiv env act0 act1
  equiv env (Procs procs0) (Procs procs1) =
    equiv env procs0 procs1
  equiv env (NewSlice cs0 r0 x0 proc0) (NewSlice cs1 r1 x1 proc1) =
    cs0 == cs1 && equiv env r0 r1 &&
    equiv env (Abs (Arg x0 (Ignored ())) proc0) (Abs (Arg x1 (Ignored ())) proc1)
  equiv env (proc0 `Dot` pp0) (proc1 `Dot` pp1)
    | Just (Prll pr0) <- proc0 ^? _Pref
    , Just (Prll pr1) <- proc1 ^? _Pref =
      let
        vd0 = ignoreArgBody <$> (actVarDecs =<< pr0)
        vd1 = ignoreArgBody <$> (actVarDecs =<< pr1)
      in
      equiv env (pr0, Telescope vd0 pp0)
                (pr1, Telescope vd1 pp1)
  equiv env (LetP defs0 p0) (LetP defs1 p1) =
    equiv env (Scoped ø defs0 p0) (Scoped ø defs1 p1)
  equiv env (LetP defs0 p0) p1 =
    equiv env (Scoped ø defs0 p0) (pure p1)
  equiv env p0 (LetP defs1 p1) =
    equiv env (pure p0) (Scoped ø defs1 p1)
  equiv _ Act{} _ = False
  equiv _ Procs{} _ = False
  equiv _ Dot{} _ = False
  equiv _ NewSlice{} _ = False

instance Print EqEnv where
  prt _i (EqEnv nms defs0 defs1 gdefS) =
    concatD [ txt "EqEnv" , txt "\n"
            , txt "{ _eqnms  = " , prt 0 nms   , txt "\n"
            , txt ", _edefs0 = " , prt 0 defs0 , txt "\n"
            , txt ", _edefs1 = " , prt 0 defs1 , txt "\n"
            , txt ", _egdefs = " , prt 0 gdefS , txt "\n"
            , txt "}" , txt "\n" ]
