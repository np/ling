{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Ling.Prelude (module Ling.Prelude, module X) where

import           Control.Applicative       as X
import           Control.Lens              as X hiding (Empty)
import           Control.Lens.Extras       as X (is)
import           Control.Monad             as X
import           Control.Monad.Except      as X
import           Control.Monad.Reader      as X
import           Data.Bifunctor            as X
import           Data.Foldable             as X
import           Data.Function             as X
import           Data.Functor              as X
import           Data.List                 as X (elemIndex, sort, transpose)
import           Data.Map                  as X (Map, keys, keysSet,
                                                 unionWithKey)
import qualified Data.Map                  as Map
import           Data.Maybe                as X
import           Data.Monoid               as X hiding (Dual)
import           Data.Set                  as X (Set)
import           Data.Set                  (intersection, member, notMember,
                                            union)
import qualified Data.Set                  as Set
import           Data.Traversable          as X
import           Data.Tuple                as X
import           Debug.Trace               as X
import           Language.Haskell.TH       (litP, stringE, stringL)
import           Language.Haskell.TH.Quote
import           Ling.Abs
import           Numeric.Lens              as X

type Endom a = a -> a

type EndoM m a = a -> m a

type Op2 a = a -> a -> a

type Rel a = a -> a -> Bool

type Msg = String

type Verbosity = Bool

anonName :: Name
anonName = Name "_"

data Arg a = Arg { _argName :: Name, _argBody :: a }
  deriving (Eq, Ord, Show, Read)

instance Functor Arg where
  fmap f (Arg n x) = Arg n (f x)

anonArg :: a -> Arg a
anonArg = Arg anonName

data Abs a b = Abs { _argAbs :: Arg a, _bodyAbs :: b }

instance Functor (Abs a) where
  fmap f (Abs arg x) = Abs arg (f x)

instance Bifunctor Abs where
  bimap f g (Abs arg x) = Abs (f <$> arg) (g x)

-- TODO: Rename into something like 'Telescoped' instead
data Telescope a b = Telescope { _argsTele :: [Arg a], _bodyTele :: b }

instance Functor (Telescope a) where
  fmap f (Telescope args x) = Telescope args (f x)

instance Bifunctor Telescope where
  bimap f g (Telescope args x) = Telescope (fmap f <$> args) (g x)

data Ann a b = Ann { _annotation :: a, _annotated :: b }
  deriving (Eq, Ord, Read, Show)

instance Bifunctor Ann where
  bimap f g (Ann a b) = Ann (f a) (g b)

makeLenses ''Arg
makeLenses ''Abs
makeLenses ''Telescope
makeLenses ''Ann

type Channel = Name

ø :: Monoid a => a
ø = mempty

nameString :: Iso' Name String
nameString = iso unName Name

prefName :: String -> Endom Name
prefName s n = n & nameString %~ (s ++)

suffName :: String -> Endom Name
suffName s n = n & nameString %~ (++ s)

traceShowMsg :: Show a => String -> Endom a
traceShowMsg msg x = trace (msg ++ " " ++ show x) x

debugTraceWhen :: Bool -> Msg -> Endom a
debugTraceWhen b s =
  if b
    then trace (unlines . map ("[DEBUG]  " ++) . lines $ s)
    else id

unName :: Name -> String
unName (Name x) = x

l2s :: Ord a => [a] -> Set a
l2s = Set.fromList

s2l :: Ord a => Set a -> [a]
s2l = Set.toList

l2m :: Ord k => [(k, a)] -> Map k a
l2m = Map.fromList

m2l :: Ord k => Map k a -> [(k, a)]
m2l = Map.toList

countMap :: (a -> Bool) -> Map k a -> Int
countMap p = Map.size . Map.filter p


infixr 3 ||>

(||>) :: Monad m => Bool -> m Bool -> m Bool
True ||> _ = return True
False ||> my = my


infixr 3 <||>

(<||>) :: Monad m => Op2 (m Bool)
mx <||> my = do
  x <- mx
  if x
    then return True
    else my


infixr 3 &&>

(&&>) :: Monad m => Bool -> m Bool -> m Bool
True &&> my = my
False &&> _ = return False


infixr 3 <&&>

(<&&>) :: Monad m => Op2 (m Bool)
mx <&&> my = do
  x <- mx
  if x
    then my
    else return False

infixr 4 ?|

-- Reverse infix form of "fromMaybe"
(?|) :: Maybe a -> Endom a
(?|) = flip fromMaybe

(.\\) :: At m => Setter s t m m -> Index m -> s -> t
l .\\ k = l . at k .~ Nothing

theUniqBy :: Rel a -> [a] -> Maybe a
theUniqBy eq (x:xs)
  | all (eq x) xs = Just x
theUniqBy _ _ = Nothing

theUniq :: Eq a => [a] -> Maybe a
theUniq = theUniqBy (==)

-- Given a list of sets, return the set of elements which are redundant, namely appear more than
-- once. `redudant` can be used to check the disjointness of sets. Indeed if the result is empty all
-- the sets are disjoint, a non-empty result can be used to report errors.
redundant :: Ord a => [Set a] -> Set a
redundant = snd . foldr f ø
  where
    f xs (acc, res) =
      (acc `union` xs, (acc `intersection` xs) `union` res)

subList :: Eq a => Rel [a]
subList []    _  = True
subList (_:_) [] = False
subList (x:xs) (y:ys)
  | x == y    = xs     `subList` ys
  | otherwise = (x:xs) `subList` ys

-- TODO: What is the best threshold between repeatdly deleting elements from a map and filtering the
-- whole map?
deleteList :: Ord k => [k] -> Endom (Map k a)
deleteList = \case
  []  -> id
  [k] -> Map.delete k
  ks  -> let sks = l2s ks in
         Map.filterWithKey (\k _ -> k `notMember` sks)

rmDups :: Eq a => [a] -> [a]
rmDups (x1:x2:xs) | x1 == x2  = rmDups (x1 : xs)
                  | otherwise = x1 : rmDups (x2 : xs)
rmDups xs                     = xs

substPred :: (a -> Bool, s) -> Endom (a -> s)
substPred (p, t) var v
  | p v = t
  | otherwise = var v

substMember :: Ord a => (Set a, s) -> Endom (a -> s)
substMember (xs, t) = substPred ((`member` xs), t)

subst1 :: Eq a => (a, s) -> Endom (a -> s)
subst1 (x, y) = substPred ((==) x, y)

hasKey :: At m => Index m -> Getter m Bool
hasKey k = to $ has (at k . _Just)

hasNoKey :: At m => Index m -> Getter m Bool
hasNoKey k = to $ has (at k . _Nothing)

{-
  The two setters must not overlap.
  If they do we can break the composition law:
  Given l, f, g such that: f.g.f.g =/= f.f.g.g
  ll = mergeSetters l l
  (ll %~ f) . (ll %~ g)
  ==
  l %~ f.f.g.g
  =/=
  l %~ f.g.f.g
  == ll %~ (f.g)
-}
mergeSetters :: ASetter s t a b -> ASetter t u a b -> Setter s u a b
mergeSetters l0 l1 = sets $ \f -> over l1 f . over l0 f

composeMapOf :: Getting (Endo r) s a -> (a -> Endom r) -> s -> Endom r
composeMapOf l = flip . foldrOf l

composeOf :: Getting (Endo r) s (Endom r) -> s -> Endom r
composeOf l = appEndo . foldOf (l . to Endo)

quasiQuoter :: String -> QuasiQuoter
quasiQuoter qqName =
  QuasiQuoter (err "expressions") (err "patterns") (err "types") (err "declarations")
  where
    err kind _ = fail $ qqName ++ ": not available in " ++ kind

list :: Traversal [a] [b] a b
list = traverse

mnot :: a -> Endom (Maybe a)
mnot a Nothing = Just a
mnot _ Just{}  = Nothing

q :: QuasiQuoter
q = (quasiQuoter "q") { quoteExp = stringE, quotePat = litP . stringL }

qFile :: QuasiQuoter
qFile = quoteFile q

lookupEnv :: Ord key => Lens' key String -> Lens' env (Map key val)
                     -> env -> key -> val
lookupEnv keyString vals env k = env ^. vals . at k ?| err
  where
    err = error $ "lookupEnv " ++ k ^. keyString . to show ++
                  " in " ++ show (env ^.. vals . to keys . each . keyString)
