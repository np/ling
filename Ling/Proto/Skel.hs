{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module Ling.Proto.Skel
  ( Skel(Act)
  , dotS
  , prllActS
  , actS
  , prune
  , subst
  , checkSkel
  ) where

import           Control.Monad.Except
import           Data.Set
import           Prelude    hiding (null)

import           Ling.Print hiding (Prll)
import           Ling.Utils

-- TODO Functor, Applicative, Monad, subst as a wrapper over >>=
data Op a = Dot | Prll | Ten a [a]
  deriving (Eq, Ord, Read, Show)

data Skel a
  = Act a
  | Zero
  | Op (Op a) (Skel a) (Skel a)
  deriving (Eq, Ord, Read, Show)

mkOp :: Eq a => Op a -> Skel a -> Skel a -> Skel a
mkOp op = f where
  Zero `f` p    = p
  p    `f` Zero = p
  p    `f` q    =
    case op of
      Dot | p == q -> q
          | Op Dot r _ <- q, p == r -> q
      _   -> Op op p q

dotS :: Eq a => Skel a -> Skel a -> Skel a
dotS = mkOp Dot

instance Eq a => Monoid (Skel a) where
  mempty = Zero
  mappend = mkOp Prll
  mconcat [] = Zero
  mconcat xs = foldr1 mappend xs

instance Print a => Print (Skel a) where
  prt i = \case
    Zero -> prPrec i 2 (doc (showString "()"))
    Act act -> prPrec i 2 (prt 0 act)
    Op op proc1 proc2 ->
      case op of
        Ten c cs -> prPrec i 1 (concatD [prt 0 c, txt "[", prt 0 cs, txt "]", nl,
                                         txt "(\n",
                                         prt 0 [proc1,proc2],
                                         txt "\n)"])
        Prll     -> prPrec i 1 (concatD [doc (showString "(\n"), prt 0 [proc1,proc2], doc (showString "\n)")])
        Dot      -> prPrec i 0 (concatD [prt 1 proc1, doc (showString ".\n"), prt 0 proc2])
  prtList _ [] = concatD []
  prtList _ [x] = prt 0 x
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString "\n|"), prt 0 xs]

actS :: Eq a => a -> Skel a -> Skel a
actS act sk = Act act `dotS` sk

prllActS :: Eq a => [a] -> Skel a -> Skel a
prllActS [act] sk = act `actS` sk
prllActS acts  sk = mconcat (Act <$> acts) `dotS` sk

subst :: Ord a => (Set a, Skel a) -> Endom (Skel a)
subst (cs, sk) = go where
  go = \case
    Zero -> Zero
    Act c
      | c `member` cs -> sk
      | otherwise     -> Act c
    Op op sk0 sk1 ->
      mkOp op (go sk0) (go sk1)

prune :: Ord a => Set a -> Endom (Skel a)
prune cs = subst (cs, Zero)

ten :: Ord a => a -> [a] -> Skel a -> Skel a -> Skel a
ten c cs sk0 sk1 = mkOp (Ten c cs) (prune scs sk0) (prune scs sk1)
  where scs = l2s cs

checkSkel :: (MonadError String m, Ord channel) =>
             channel -> [channel] -> EndoM m (Skel channel)
checkSkel c cs = fmap final . go where
  scs = l2s cs
  final (_, sk', sk'') = sk' <> sk''
  go = \case
    Zero -> return (ø, Zero, Zero)
    Act a
      | a `member` scs -> return (l2s [a], Act a, Zero)
      | otherwise      -> return (ø,       Zero,  Act a)
    Op op sk0 sk1 -> do
      (cs0, sk0', sk0'') <- go sk0
      (cs1, sk1', sk1'') <- go sk1
      let
        ics = cs0 `intersection` cs1
        ucs = cs0 `union`        cs1
      unless (null ics) $ throwError "checkSkel: non null intersection"
      (sk', sk'') <-
        case op of
          _   | null cs0 && null cs1 ->
            return (Zero, mkOp op (sk0' <> sk0'') (sk1' <> sk1''))

          Dot  | not (null cs1) && not (null cs0) ->
            throwError "checkSel: Dot"

          Dot | not (null cs0 && null cs1) ->
            return ((sk0' <> sk0'') `dotS` (sk1' <> sk1''), Zero)

          Prll | not (null cs1) && not (null cs0) ->
            return (ten c cs sk0' sk1', sk0'' <> sk1'')
          Prll | null cs0 && not (null cs1) ->
            return (sk1', sk0' <> sk0'' <> sk1'')
          Prll | null cs1 && not (null cs0) ->
            return (sk0', sk0'' <> sk1' <> sk1'')

          Ten{} ->
            throwError "checkSkel: Ten"

          _ ->
            throwError "checkSkel: IMPOSSIBLE"
      return (ucs, sk', sk'')
