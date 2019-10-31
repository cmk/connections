-- {-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
module Data.Prd (
    module Data.Prd
  , Down(..)
) where

import Control.Applicative
import Control.Monad
import Data.Data (Data, Typeable)
import Data.Function
import Data.Int as Int (Int, Int8, Int16, Int32, Int64)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (First, Last)
import Data.Ord (Down(..))
import Data.Ratio
import Data.Word (Word, Word8, Word16, Word32, Word64)
import GHC.Generics (Generic, Generic1)
import GHC.Real
import Numeric.Natural

import qualified Data.Semigroup as S
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq

infix 4 <~, >~, /~, ~~, =~, ?~, `pgt`, `pge`, `peq`, `pne`, `ple`, `plt`

infix 4 `lt`, `gt`, `le`, `ge`, `eq`, `ne`, `pmax`, `pmin`


-- | A partial order on the set /a/.
--
-- A poset relation '<~' must satisfy the following three partial order axioms:
--
-- \( \forall x: x \leq x \) (reflexivity)
-- 
-- \( \forall a, b: (a \leq b) \Leftrightarrow \neg (b \leq a) \) (anti-symmetry)
--
-- \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \) (transitivity)
--
-- If a prior equality relation is available, then a valid @Prd a@ instance may be derived from a semiorder relation 'lt' as:
--
-- @
-- x '<~' y = 'lt' x y '||' x '==' y
-- @
--
-- If /a/ is derived from a semiorder then the definition of 'lt' must satisfy 
-- the three semiorder axioms:
--
-- \( \forall x, y: x \lt y \Rightarrow \neg y \lt x \) (asymmetry)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \sim z \wedge z \lt w \Rightarrow x \lt w \) (2-2 chain)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \lt z \wedge y \sim w \Rightarrow \neg (x \sim w \wedge z \sim w) \) (3-1 chain)
--
-- The poset axioms on '<~' then follow from the first & second axioms on 'lt',
-- however the converse is not true. While the first semiorder axiom on 'lt' follows, the second 
-- and third semiorder axioms forbid partial orders of four items forming two disjoint chains: 
--
-- * the second axiom forbids two chains of two items each (the (2+2) free poset)
-- * the third axiom forbids a three-item chain with one unrelated item
--
-- See also the wikipedia definitions of <https://en.wikipedia.org/wiki/Partially_ordered_set partially ordered set>
-- and <https://en.wikipedia.org/wiki/Semiorder semiorder>.
--
class Prd a where
  {-# MINIMAL (<~) | (>~) #-} 

  -- | Non-strict partial order relation on /a/.
  --
  -- '<~' is reflexive, anti-symmetric, and transitive.
  --
  (<~) :: a -> a -> Bool
  (<~) = flip (>~)

  -- | Converse non-strict partial order relation on /a/.
  --
  -- '>~' is reflexive, anti-symmetric, and transitive.
  --
  (>~) :: a -> a -> Bool
  (>~) = flip (<~)

  -- | Equivalence relation on /a/.
  --
  -- '=~' is reflexive, symmetric, and transitive.
  --
  -- @ x =~ y = maybe False (== EQ) (pcomparePrd x y)
  --
  -- If /a/ implements 'Eq' then (ideally) @x =~ y = x == y@.
  --
  (=~) :: Prd a => a -> a -> Bool
  x =~ y = x <~ y && x >~ y

  -- | Comparability relation on /a/. 
  --
  -- '?~' is reflexive, symmetric, and transitive.
  --
  -- @ x ?~ y = maybe False (const True) (pcomparePrd x y) @
  --
  -- If /a/ implements 'Ord' then (ideally) @x ?~ y = True@.
  --
  (?~) :: Prd a => a -> a -> Bool
  x ?~ y = x <~ y || x >~ y

  -- | Partial version of 'Data.Ord.compare'.
  --
  pcompare :: Eq a => a -> a -> Maybe Ordering
  pcompare x y
    | x `lt` y  = Just LT
    | x  ==  y  = Just EQ
    | x `gt` y  = Just GT
    | otherwise = Nothing


-- | Similarity relation on /a/. 
--
-- '~~' is reflexive and symmetric, but not necessarily transitive.
--
-- Note this is only equivalent to '==' in a total (i.e. linear) order.
--
(~~) :: Eq a => Prd a => a -> a -> Bool
x ~~ y = not (x `lt` y) && not (x `gt` y)

-- | Negation of '~~'.
--
(/~) :: Eq a => Prd a => a -> a -> Bool
x /~ y = not $ x ~~ y


-- | Version of 'pcompare' that uses the derived equivalence relation.
--
-- This can be useful if there is no 'Eq' instance or if it is
-- compromised, for example when /a/ is a floating point number.
--
pcomparePrd :: Prd a => a -> a -> Maybe Ordering
pcomparePrd x y 
  | x <~ y = Just $ if y <~ x then EQ else LT
  | y <~ x = Just GT
  | otherwise = Nothing

-- | Version of 'pcompare' that uses 'compare'.
--
pcompareOrd :: Ord a => a -> a -> Maybe Ordering
pcompareOrd x y = Just $ x `compare` y

-- | Prefix version of '=~'.
--
-- @ eq x y = maybe False (== EQ) (pcomparePrd x y)
--
eq :: Prd a => a -> a -> Bool
x `eq` y = x <~ y && x >~ y

-- | Negation of 'eq'.
--
-- @ ne x y = maybe False (/= EQ) (pcomparePrd x y)
--
ne :: Prd a => a -> a -> Bool
x `ne` y = not $ x `eq` y

-- | Prefix version of '<~'.
--
-- @ le x y = maybe False (<= EQ) (pcomparePrd x y)
--
le :: Prd a => a -> a -> Bool
x `le` y = x <~ y

-- | Prefix version of '>~'.
--
-- @ ge x y = maybe False (>= EQ) (pcomparePrd x y)
--
ge :: Prd a => a -> a -> Bool
x `ge` y = x >~ y

-- | Strict partial order relation on /a/.
--
-- 'lt' is irreflexive, asymmetric, and transitive.
--
-- @ lt x y = maybe False (< EQ) (pcompare x y) @
--
-- If /a/ implements 'Ord' then (ideally) @x `lt` y = x < y@.
--
lt :: Eq a => Prd a => a -> a -> Bool
x `lt` y | x /= x || y /= y = False -- guard on lawless 0/0 cases
         | otherwise        = x <~ y && x /= y

-- | Converse strict partial order relation on /a/.
--
-- 'gt' is irreflexive, asymmetric, and transitive.
--
-- @ gt x y = maybe False (> EQ) (pcompare x y) @
--
-- If /a/ implements 'Ord' then (ideally) @x `gt` y = x > y@.
--
gt :: Eq a => Prd a => a -> a -> Bool
x `gt` y | x /= x || y /= y = False 
         | otherwise        = x >~ y && x /= y

-- | A partial version of ('=~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
peq  :: Eq a => Prd a => a -> a -> Maybe Bool
peq x y = case x `pcompare` y of
     Just EQ -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of ('/~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pne :: Eq a => Prd a => a -> a -> Maybe Bool
pne x y = case x `pcompare` y of
     Just EQ -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('<~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
ple :: Eq a => Prd a => a -> a -> Maybe Bool
ple x y = case x `pcompare` y of
     Just GT -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('>~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pge :: Eq a => Prd a => a -> a -> Maybe Bool
pge x y = case x `pcompare` y of
     Just LT -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('<')  
-- 
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @lt x y == maybe False id $ plt x y@
--
plt :: Eq a => Prd a => a -> a -> Maybe Bool
plt x y = case x `pcompare` y of
     Just LT -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of ('>')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @gt x y == maybe False id $ pgt x y@
--
pgt :: Eq a => Prd a => a -> a -> Maybe Bool
pgt x y = case x `pcompare` y of
     Just GT -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of 'Data.Ord.max'. 
--
-- Default instance returns the connr argument in the case of equality.
--
pmax :: Eq a => Prd a => a -> a -> Maybe a
pmax x y = do
  o <- pcompare x y
  case o of
    GT -> Just x
    EQ -> Just y
    LT -> Just y

pjoin :: Eq a => Min a => Foldable f => f a -> Maybe a
pjoin = foldM pmax minimal

-- | A partial version of 'Data.Ord.min'. 
--
-- Default instance returns the connr argument in the case of equality.
--
pmin :: Eq a => Prd a => a -> a -> Maybe a
pmin x y = do
  o <- pcompare x y
  case o of
    GT -> Just y
    EQ -> Just x
    LT -> Just x

pmeet :: Eq a => Max a => Foldable f => f a -> Maybe a
pmeet = foldM pmin maximal

sign :: Eq a => Num a => Prd a => a -> Maybe Ordering
sign x = pcompare x 0

zero :: Eq a => Num a => Prd a => a -> Bool
zero x = sign x == Just EQ

positive :: Eq a => Num a => Prd a => a -> Bool
positive x = sign x == Just GT

negative :: Eq a => Num a => Prd a => a -> Bool
negative x = sign x == Just LT

indeterminate :: Eq a => Num a => Prd a => a -> Bool
indeterminate x = sign x == Nothing


---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

instance Prd Bool where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Char where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Integer where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int where 
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int8 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int16 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int32 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int64 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Natural where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word8 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word16 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word32 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word64 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Ordering where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd a => Prd [a] where
    {-# SPECIALISE instance Prd [Char] #-}
    [] <~ _     = True
    (_:_) <~ [] = False
    (x:xs) <~ (y:ys) = x <~ y && xs <~ ys

{-
    pcompare []     []     = Just EQ
    pcompare []     (_:_)  = Just LT
    pcompare (_:_)  []     = Just GT
    pcompare (x:xs) (y:ys) = case pcompare x y of
                                Just EQ -> pcompare xs ys
                                other   -> other
-}

instance Prd a => Prd (NonEmpty a) where
    (x :| xs) <~ (y :| ys) = x <~ y && xs <~ ys

instance Prd a => Prd (Down a) where
    x <~ y = y <~ x

-- Canonically ordered.
instance Prd a => Prd (Dual a) where
    x <~ y = y <~ x

instance Prd Any where
    Any x <~ Any y = x <~ y

instance Prd All where
    All x <~ All y = y <~ x

{-

-- | 'First a' forms a pre-dioid for any semigroup @a@.
instance (Eq a, Semigroup a) => Prd (S.First a) where 
    (<~) = (==)

instance Ord a => Prd (S.Max a) where 
    pcompare (S.Max x) (S.Max y) = Just $ compare x y

instance Ord a => Prd (S.Min a) where 
    pcompare (S.Min x) (S.Min y) = Just $ compare y x

-}

instance Prd Float where
    x <~ y | x /= x && y /= y = True 
           | x /= x || y /= y = False
           | otherwise        = x <= y
{-
    pcompare x y | x /= x && y /= y = Just EQ 
                 | x /= x || y /= y = Nothing
                 | otherwise        = pcompareOrd x y

    x `eq` y | x /= x && y /= y = True
             | x /= x || y /= y = False
             | otherwise = x == y

    x `lt` y | x /= x || y /= y = False
             | otherwise = shift 2 x P.< y
-}



instance Prd Double where
    x <~ y | x /= x && y /= y = True 
           | x /= x || y /= y = False
           | otherwise        = x <= y

instance  (Prd a, Integral a)  => Prd (Ratio a)  where
    {-# SPECIALIZE instance Prd Rational #-}
    (x:%y) <~ (x':%y') | (x `eq` 0 && y `eq` 0) || (x' `eq` 0 && y' `eq` 0) = False
                         | otherwise = x * y' <~ x' * y

-- Canonical semigroup ordering
instance Prd a => Prd (Maybe a) where
    Just a <~ Just b = a <~ b
    x@Just{} <~ Nothing = False
    Nothing <~ _ = True

-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (Either a b) where
    Right a <~ Right b  = a <~ b
    Right _ <~ _        = False
    
    Left e <~ Left f   = e <~ f
    Left _ <~ _        = True
 
instance Prd () where 
    pcompare _ _ = Just EQ
    _ <~ _ = True

-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (a, b) where 
  (a,b) <~ (i,j) = a <~ i && b <~ j

instance (Prd a, Prd b, Prd c) => Prd (a, b, c) where 
  (a,b,c) <~ (i,j,k) = a <~ i && b <~ j && c <~ k

instance (Prd a, Prd b, Prd c, Prd d) => Prd (a, b, c, d) where 
  (a,b,c,d) <~ (i,j,k,l) = a <~ i && b <~ j && c <~ k && d <~ l

instance (Prd a, Prd b, Prd c, Prd d, Prd e) => Prd (a, b, c, d, e) where 
  (a,b,c,d,e) <~ (i,j,k,l,m) = a <~ i && b <~ j && c <~ k && d <~ l && e <~ m

instance Ord a => Prd (Set.Set a) where
    (<~) = Set.isSubsetOf

instance (Ord k, Prd a) => Prd (Map.Map k a) where
    (<~) = Map.isSubmapOfBy (<~)

instance Prd a => Prd (IntMap.IntMap a) where
    (<~) = IntMap.isSubmapOfBy (<~)

instance Prd IntSet.IntSet where
    (<~) = IntSet.isSubsetOf


-- Helper type for 'DerivingVia'
newtype Ordered a = Ordered { getOrdered :: a }
  deriving ( Eq, Ord, Show, Data, Typeable, Generic, Generic1, Functor, Foldable, Traversable)

instance Ord a => Prd (Ordered a) where
    (<~) = (<=)

type Bound a = (Min a, Max a) 

-- | Min element of a partially ordered set.
-- 
-- \( \forall x: x \ge minimal \)
--
-- This means that 'minimal' must be comparable to all values in /a/.
--
class Prd a => Min a where
    minimal :: a

instance Min () where minimal = ()

instance Min Natural where minimal = 0

instance Min Bool where minimal = minBound

instance Min Ordering where minimal = minBound

instance Min Int where minimal = minBound

instance Min Int8 where minimal = minBound

instance Min Int16 where minimal = minBound

instance Min Int32 where minimal = minBound

instance Min Int64 where minimal = minBound

instance Min Word where minimal = minBound

instance Min Word8 where minimal = minBound

instance Min Word16 where minimal = minBound

instance Min Word32 where minimal = minBound

instance Min Word64 where minimal = minBound 

instance Prd a => Min (IntMap.IntMap a) where
    minimal = IntMap.empty

instance Ord a => Min (Set.Set a) where
    minimal = Set.empty

instance (Ord k, Prd a) => Min (Map.Map k a) where
    minimal = Map.empty

instance (Min a, Min b) => Min (a, b) where
    minimal = (minimal, minimal)

instance (Min a, Prd b) => Min (Either a b) where
    minimal = Left minimal

instance Prd a => Min (Maybe a) where
    minimal = Nothing 

instance Max a => Min (Down a) where
    minimal = Down maximal

-- | Max element of a partially ordered set.
--
-- \( \forall x: x \le maximal \)
--
-- This means that 'maximal' must be comparable to all values in /a/.
--
class Prd a => Max a where
    maximal :: a

instance Max () where maximal = ()

instance Max Bool where maximal = maxBound

instance Max Ordering where maximal = maxBound

instance Max Int where maximal = maxBound

instance Max Int8 where maximal = maxBound

instance Max Int16 where maximal = maxBound

instance Max Int32 where maximal = maxBound

instance Max Int64 where maximal = maxBound

instance Max Word where maximal = maxBound

instance Max Word8 where maximal = maxBound

instance Max Word16 where maximal = maxBound

instance Max Word32 where maximal = maxBound

instance Max Word64 where maximal = maxBound

instance (Max a, Max b) => Max (a, b) where
    maximal = (maximal, maximal)

instance (Prd a, Max b) => Max (Either a b) where
    maximal = Right maximal

instance Max a => Max (Maybe a) where
    maximal = Just maximal

instance Min a => Max (Down a) where
    maximal = Down minimal

{-
instance (Universe a, Prd a) => Prd (k -> a) where

instance Min a => Min (k -> a) where
    minimal = const minimal

instance Max a => Max (k -> a) where
    maximal = const maximal
-}
 

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pred rel f seed = go seed
  where go x | x' `rel` x = x
             | pred x = x
             | otherwise = go x'
          where x' = f x

{-# INLINE while #-}
while :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while pred rel f seed = go seed
  where go x | x' `rel` x = x
             | not (pred x') = x
             | otherwise = go x'
          where x' = f x

{-
while' :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while' pred rel f seed = go seed f
  where go x | x' `rel` x = id
             | not (pred x') = id
             | otherwise = go x' . f
          where x' = f x
-}

-- | Greatest (resp. least) fixed point of a monitone (resp. antitone) function. 
--
-- Does not check that the function is monitone (resp. antitone).
--
-- See also < http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem >.
--
{-# INLINE fixed #-}
fixed :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixed = while (\_ -> True)

