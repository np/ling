{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Ling.Prelude (module Ling.Prelude, module X) where

import           Control.Applicative       as X
import           Control.Lens              as X hiding (Empty)
import           Control.Lens.Extras       as X (is)
import           Control.Monad             as X
import           Control.Monad.Except      as X
import           Control.Monad.Reader      as X
import           Data.Bifoldable           as X
import           Data.Bifunctor            as X
import           Data.Bitraversable        as X
import           Data.ByteString.Lazy.Lens as BL
import           Data.Digest.Pure.SHA      (sha256, showDigest)
import           Data.Foldable             as X
import           Data.Function             as X
import           Data.Functor              as X
import           Data.List                 as X (elemIndex, partition, sort,
                                                 transpose)
import           Data.List.Lens            as X
import           Data.Map                  as X (Map, keys, keysSet,
                                                 unionWithKey)
import qualified Data.Map                  as Map
import           Data.Maybe                as X
import           Data.Monoid               as X hiding (Dual)
import           Data.Set                  as X (Set)
import           Data.Set                  (intersection, member, notMember,
                                            union, insert)
import qualified Data.Set                  as Set
import           Data.Set.Lens             as X
import           Data.Traversable          as X
import           Data.Tuple                as X
import           Debug.Trace               as X
import           Language.Haskell.TH       (litP, stringE, stringL)
import           Language.Haskell.TH.Quote
import           Ling.Abs
import           Numeric.Lens              as X
import           Text.Show.Pretty          as X (ppShow)

type Endom a = a -> a

type EndoPrism a = Prism' a a

type EndoM m a = a -> m a

type Op2 a = a -> a -> a

type Rel a = a -> a -> Bool

type Msg = String

type Verbosity = Bool

newtype Prll a = Prll { _unPrll :: [a] }
  deriving (Eq, Ord, Show, Read)

makePrisms ''Prll
makeLenses ''Prll

ø :: Monoid a => a
ø = mempty

instance Semigroup (Prll a) where
  Prll ps <> Prll qs = Prll (ps <> qs)

instance Monoid (Prll a) where
  mempty = Prll ø

instance Each (Prll a) (Prll b) a b where
  each = _Prll . each

newtype Order a = Order { _unOrder :: [a] }
  deriving (Eq, Ord, Show, Read)

makePrisms ''Order
makeLenses ''Order

instance Semigroup (Order a) where
  Order x <> Order y = Order (x <> y)

instance Monoid (Order a) where
  mempty = Order []

instance Each (Order a) (Order b) a b where
  each = _Order . each

anonName :: Name
anonName = Name "_"

data Arg a = Arg { _argName :: Name, _argBody :: a }
  deriving (Eq, Ord, Show, Read)

makePrisms ''Arg
makeLenses ''Arg

instance Functor Arg where fmap = over argBody

instance Each (Arg a) (Arg b) a b where
  each = argBody

instance t ~ Arg a' => Rewrapped (Arg a) t
instance Wrapped (Arg a) where
  type Unwrapped (Arg a) = (Name, a)
  _Wrapped' = _Arg

anonArg :: a -> Arg a
anonArg = Arg anonName

data Abs a b = Abs { _argAbs :: Arg a, _bodyAbs :: b }

makePrisms ''Abs
makeLenses ''Abs

instance Functor (Abs a) where fmap = over bodyAbs

instance Bifunctor Abs where
  bimap f g (Abs arg x) = Abs (f <$> arg) (g x)

instance Bifoldable Abs where
  bifoldMap = bifoldMapDefault

instance Bitraversable Abs where
  bitraverse f g (Abs arg x) = Abs <$> argBody f arg <*> g x

instance t ~ Abs a' b' => Rewrapped (Abs a b) t
instance Wrapped (Abs a b) where
  type Unwrapped (Abs a b) = (Arg a, b)
  _Wrapped' = _Abs

-- TODO: Rename into something like 'Telescoped' instead
data Telescope a b = Telescope { _argsTele :: [Arg a], _bodyTele :: b }

makePrisms ''Telescope
makeLenses ''Telescope

instance Functor (Telescope a) where
  fmap f (Telescope args x) = Telescope args (f x)

instance Bifunctor Telescope where
  bimap f g (Telescope args x) = Telescope (fmap f <$> args) (g x)

instance Bifoldable Telescope where
  bifoldMap = bifoldMapDefault

instance Bitraversable Telescope where
  bitraverse f g (Telescope args x) = Telescope <$> (traverse . argBody) f args <*> g x

data Ann a b = Ann { _annotation :: a, _annotated :: b }
  deriving (Eq, Ord, Read, Show)

makePrisms ''Ann
makeLenses ''Ann

instance Bifunctor Ann where
  bimap f g (Ann a b) = Ann (f a) (g b)

instance Bifoldable Ann where
  bifoldMap = bifoldMapDefault

instance Bitraversable Ann where
  bitraverse f g (Ann a b) = Ann <$> f a <*> g b

instance t ~ Ann a' b' => Rewrapped (Ann a b) t
instance Wrapped (Ann a b) where
  type Unwrapped (Ann a b) = (a, b)
  _Wrapped' = _Ann

type Channel = Name

_Name :: Iso' Name String
_Name = iso (\(Name x) -> x) Name

unName :: Iso' String Name
unName = from _Name

_OpName :: Iso' OpName String
_OpName = iso (\(OpName x) -> x) OpName

unOpName :: Iso' String OpName
unOpName = from _OpName

indented :: Int -> Fold String String
indented n = lined . re (prefixed (replicate n ' '))

isInternalName :: Name -> Bool
isInternalName (Name s) = '#' `elem` s

internalNameFor :: Show a => a -> EndoPrism Name
internalNameFor = suffixedName . hash256 . show

prefixedName :: String -> EndoPrism Name
prefixedName s = _Name . prefixed (s++"#") . unName

suffixedName :: String -> EndoPrism Name
suffixedName s = _Name . suffixed ('#':s) . unName

suffixedChan :: String -> EndoPrism Channel
suffixedChan = suffixedName

prefixedChan :: String -> EndoPrism Channel
prefixedChan = prefixedName

-- infixed = match "_[^_]*_"
infixed :: Prism' Name OpName
infixed = _Name . prism' con pat . unOpName
  where
    con x = '_' : x ++ "_"
    pat ('_':xs@(_:_:_))
      | let s = init xs, last xs == '_' && '_' `notElem` s = Just s
    pat _ = Nothing

flat3 :: Iso (a,(b,c)) (d,(e,f)) (a,b,c) (d,e,f)
flat3 = iso (\(x,(y,z))->(x,y,z)) (\(x,y,z)->(x,(y,z)))

traceShowMsg :: Show a => String -> Endom a
traceShowMsg msg x = trace (msg ++ " " ++ show x) x

debugTraceWhen :: Bool -> Msg -> Endom a
debugTraceWhen b s =
  if b
    then trace (unlines . map ("[DEBUG]  " ++) . lines $ s)
    else id

type UsedNames = Set Name

avoidUsed :: Name -> Name -> UsedNames -> (Name, UsedNames)
avoidUsed suggestion basename used = go allNames where
  allPrefixes = ["x", "y", "z"] ++ ["x" ++ show (i :: Int) | i <- [0..]]
  allNames = (if suggestion == anonName then id else (suggestion :)) $
             [ prefixedName p # basename | p <- allPrefixes ]
  go names | x `member` used = go (tail names)
           | otherwise       = (x, insert x used)
    where x = head names

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
    err :: MonadFail m => String -> a -> m b
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

hash256 :: String -> String
hash256 = showDigest . sha256 . view BL.packedChars

data FinEndom a = FinEndom { _finMap :: !(Map a a), _finDflt :: !a }
  deriving (Ord, Show, Read)

mkFinEndom :: (Enum a, Ord a) => Endom a -> FinEndom a
mkFinEndom f = FinEndom (l2m (filter ((/=d).snd) g)) d
  where
  -- TODO pick the most recurring element
    (_,d):g = [(x, f x) | x <- [toEnum 0..]]

evalFinEndom :: Ord a => FinEndom a -> Endom a
evalFinEndom (FinEndom m d) a = m ^. at a ?| d

instance (Enum a, Ord a) => Semigroup (FinEndom a) where
  f <> g = mkFinEndom (evalFinEndom f . evalFinEndom g)

instance (Enum a, Ord a) => Monoid (FinEndom a) where
  mempty = mkFinEndom id

constEndom :: Ord a => a -> FinEndom a
constEndom = FinEndom ø

ifEndom :: Ord a => a -> a -> FinEndom a -> FinEndom a
ifEndom c t (FinEndom m d)
  | t == d    = FinEndom (m & sans c)         d
  | otherwise = FinEndom (m & at c .~ Just t) d

finEndomMap :: (Enum a, Ord a) => FinEndom a -> Map a a
finEndomMap (FinEndom m d) = foldr (\a -> at a %~ f) m [toEnum 0..]
  where f Nothing = Just d
        f x       = x

instance (Enum a, Ord a) => Eq (FinEndom a) where
  f == g = all (\x -> evalFinEndom f x == evalFinEndom g x) [toEnum 0..]

makePrisms ''FinEndom
makeLenses ''FinEndom
