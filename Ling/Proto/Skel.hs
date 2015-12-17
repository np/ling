{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ling.Proto.Skel (
    Skel(Act),
    combineS,
    dotS,
    unknownS,
    prllActS,
    dotActS,
    actS,
    prune,
    select,
    subst,
    dotChannelSet,
    check,
    ) where

import           Data.Set     hiding (foldr)
import           Prelude      hiding (null)

import           Ling.Norm    (TraverseKind (..))
import           Ling.Prelude hiding (null, op, q, Prll)
import           Ling.Print

-- A way to deal with Unknown would be to stick an identifier on each of them. Then the normal
-- equality could be used safely. One way would be to use an `IORef ()`
data Op = Dot
        | Prll !Bool
        | Unknown
  deriving (Eq, Ord, Read, Show)

-- Use compat instead of (==) to avoid treating two unknowns as the same.
compat :: Rel Op
Dot    `compat` Dot     = True
Prll b `compat` Prll b' = b == b'
_      `compat` _       = False -- Yes Unknown /= Unknown

data Skel a = Act a
            | Zero
            | Op !Op (Skel a) (Skel a)
  deriving (Eq, Ord, Read, Show)

mkOp :: Eq a => Op -> Op2 (Skel a)
mkOp op = go where
  Zero  `go` p     = p
  p     `go` Zero  = p

  Act c `go` p
    | Prll _ <- op,
      c `elemS` p  = p

    -- Avoid redundancies on the left: c * (c * sk) --> c * sk
    | Op op' (Act d) _ <- p,
      op `compat` op',
      c == d       = p

  p     `go` Act c
    | Prll _ <- op,
      c `elemS` p  = p

  Act c `go` Act d
    | c == d       = Act d

  p     `go` q

    -- Right nesting: (x * y) * z --> x * (y * z)
    | Op op' p0 p1 <- p,
      op `compat` op'     = mkOp op p0 (mkOp op p1 q)

    | otherwise           = Op op p q

skel :: (Ord a, Ord b) => Traversal (Skel a) (Skel b) a b
skel f = \case
  Zero -> pure Zero
  Act a -> Act <$> f a
  Op op sk0 sk1 -> mkOp op <$> skel f sk0 <*> skel f sk1

fcSkel :: (Eq a, Ord a) => Skel a -> Set a
fcSkel = setOf skel

infixr 4 `dotS`

dotS :: Eq a => Op2 (Skel a)
dotS = mkOp Dot

unknownS :: Eq a => Op2 (Skel a)
unknownS = mkOp Unknown

combineS :: Eq a => TraverseKind -> Op2 (Skel a)
combineS = \case
  ParK -> unknownS
  TenK -> mappend
  SeqK -> dotS

instance Eq a => Monoid (Skel a) where
  mempty = Zero
  mappend = mkOp (Prll True)
  mconcat [] = Zero
  mconcat xs = foldr1 mappend xs

instance Print Op where
  prt _ = txt . \case
    Prll True  -> "\n|"
    Prll False -> "\nX"
    Unknown    -> "\n⁇"
    Dot        -> ".\n"

instance (Print a, Eq a) => Print (Skel a) where
  prt _ = \case
    Zero -> txt "()"
    Act act -> prt 0 act
    Op op proc1 proc2 ->
      concatD [ txt "(\n"
              , prt 0 proc1
              , prt 0 op
              , prt 0 proc2
              , txt "\n)"]

  prtList _ = prt 0 . mconcat

infixr 4 `actS`

actS :: Eq a => a -> Endom (Skel a)
actS act sk = Act act `dotS` sk


infixr 4 `prllActS`

prllActS :: Eq a => [a] -> Endom (Skel a)
prllActS [act] sk = act `actS` sk
prllActS acts  sk = mconcat (Act <$> acts) `dotS` sk

infixr 4 `dotActS`

dotActS :: Eq a => [a] -> Endom (Skel a)
dotActS []         sk = sk
dotActS (act:acts) sk = act `actS` acts `dotActS` sk

elemS :: Eq a => a -> Skel a -> Bool
elemS c0 = go
  where
    go = \case
      Zero         -> False
      Act c        -> c == c0
      Op _ sk0 sk1 -> go sk0 || go sk1

subst :: Eq b => (a -> Skel b) -> Skel a -> Skel b
subst act = go
  where
    go = \case
      Zero          -> Zero
      Act c         -> act c
      Op op sk0 sk1 -> mkOp op (go sk0) (go sk1)

prune :: Ord a => Set a -> Endom (Skel a)
prune cs = subst (substMember (cs, Zero) Act)

select :: Ord a => Set a -> Endom (Skel a)
select cs = subst (substPred ((`notMember` cs), Zero) Act)

-- TODO: What about unknown?
-- If the meaning of unknown gets tweak to mean
-- "in some order but not in parallel", then
-- sequencingOp Unknown = True
sequencingOp :: Op -> Bool
sequencingOp Dot = True
sequencingOp _   = False

dotChannelSet :: Ord a => Skel a -> Maybe (Set a)
dotChannelSet = \case
  Zero -> pure ø
  Act c -> pure (l2s [c])
  Op op sk0 sk1
    | sequencingOp op -> union <$> dotChannelSet sk0 <*> dotChannelSet sk1
    | otherwise -> Nothing

mAct :: Maybe channel -> Skel channel
mAct Nothing  = Zero
mAct (Just c) = Act c

prllFalse :: Ord a => Maybe a -> Set a -> Op2 (Skel a)
prllFalse c scs sk0 sk1 = mkOp (Prll False) (go sk0) (go sk1)
  where
    go   = subst (substMember (scs, mAct c) Act)

check :: (MonadError String m, Ord channel, Show channel) =>
         Maybe channel -> [channel] -> EndoM m (Skel channel)
check c cs = fmap (uncurry (<>)) . go where
  scs = l2s cs
  -- Given a skeleton sk, `go` returns a pair (sk', sk'')
  -- sk'  is a skeleton with    occurrences from scs
  -- sk'' is a skeleton without occurrences from scs
  -- sk should be equivalent to sk' | sk''
  go = \case
    Zero -> return (Zero, Zero)
    Act a
      | a `member` scs -> return (Act a, Zero)
      | otherwise      -> return (Zero,  Act a)
    Op op sk0 sk1 -> do
      (sk0', sk0'') <- go sk0
      (sk1', sk1'') <- go sk1
      let
        cs0 = scs `intersection` fcSkel sk0'
        cs1 = scs `intersection` fcSkel sk1'
        cs' = cs0 `union` cs1
      -- We could throw an error when the intersection of cs0 and cs1
      -- is not null, however these errors are also caught elsewhere
      -- (when merging parallel protocols for instance)
      -- One case we want to let pass is when the same channel is used
      -- twice on one side:
      -- c[d,e] (send d 1 | send e 2. send a 3. send e 4)
      -- Here the skeleton is: `(d | e.a.e)`, the channel `e` appear twice
      -- and we chose to keep the ordering. We need the reconstruction of:
      -- `e.a.e` not to raise an error.
      case op of
        _   | null cs0 && null cs1 ->
          return (Zero, mkOp op (sk0' <> sk0'') (sk1' <> sk1''))

        Prll True | not (null cs1) && not (null cs0) ->
          return (prllFalse c cs' sk0' sk1', sk0'' <> sk1'')
        Prll True | null cs0 && not (null cs1) ->
          return (sk1', sk0' <> sk0'' <> sk1'')
        Prll True | null cs1 && not (null cs0) ->
          return (sk0', sk0'' <> sk1' <> sk1'')

        _ | not (null cs1) && not (null cs0) && cs0 /= cs1 ->
          throwError $ "checkSel: " ++ show op

        _ ->
          return (mkOp op (sk0' <> sk0'') (sk1' <> sk1''), Zero)
