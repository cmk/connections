{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE Safe              #-}

module Data.Order.Interval (
    Interval()
  , imap
  , (...)
  , iempty
  , singleton
  , contains
  , endpts
  --, above
  --, below
  --, interval
  -- * Floating point intervals
  , open32
  , open32L
  , open32R
  , open64
  , open64L
  , open64R
) where

import safe Data.Bifunctor (bimap)
import safe Data.Order
import safe Data.Order.Syntax
import safe Prelude hiding (Ord(..), Eq(..), Bounded, until)
import safe qualified Data.Eq as Eq
import safe qualified Data.Connection.Float as F32
import safe qualified Data.Connection.Double as F64

---------------------------------------------------------------------
-- Intervals
---------------------------------------------------------------------

-- | An interval in a poset /P/.
--
-- An interval in a poset /P/ is a subset /I/ of /P/ with the following property:
--
-- \( \forall x, y \in I, z \in P: x \leq z \leq y \Rightarrow z \in I \)
--
data Interval a = Empty | I !a !a deriving Show

-- | Map over an interval.
--
-- /Note/ this is not a functor, as a non-monotonic map
-- may cause the interval to collapse to the iempty interval.
--
imap :: Preorder b => (a -> b) -> Interval a -> Interval b
imap f = maybe iempty (uncurry (...)) . fmap (bimap f f) . endpts

infix 3 ...

-- | Construct an interval from a pair of points.
--
-- /Note/: Endpoints are preorder-sorted. If /pcompare x y = Nothing/
-- then the resulting interval will be empty.
-- 
(...) :: Preorder a => a -> a -> Interval a
x ... y = case pcompare x y of
  Nothing -> Empty
  Just GT -> I y x
  Just _  -> I x y
{-# INLINE (...) #-}

-- | The iempty interval.
--
-- >>> iempty
-- Empty
--
iempty :: Interval a
iempty = Empty
{-# INLINE iempty #-}

-- | Construct an interval containing a single point.
--
-- >>> singleton 1
-- 1 ... 1
--
singleton :: a -> Interval a
singleton a = I a a
{-# INLINE singleton #-}

-- | Obtain the endpoints of an interval.
--
endpts :: Interval a -> Maybe (a, a)
endpts Empty = Nothing
endpts (I x y) = Just (x, y)
{-# INLINE endpts #-}

contains :: Preorder a => Interval a -> a -> Bool
contains Empty _ = False
contains (I x y) p = x <~ p && p <~ y

{-


-- | \( X_\geq(x) = \{ y \in X | y \geq x \} \)
--
-- Construct the upper set of an element /x/.
--
-- This function is monotone:
--
-- > x <~ y <=> above x <~ above y
--
-- by the Yoneda lemma for preorders.
--
above :: Maximal a => a -> Interval a
above x = x ... maximal
{-# INLINE above #-}

-- | \( X_\leq(x) = \{ y \in X | y \leq x \} \)
--
-- Construct the lower set of an element /x/.
--
-- This function is antitone:
--
-- > x <~ y <=> below x >~ below y
--
below :: Minimal a => a -> Interval a
below x = minimal ... x
{-# INLINE below #-}


-}

---------------------------------------------------------------------
-- Floating point intervals
---------------------------------------------------------------------


-- | Construnct an open interval.
--
-- >>> contains 1 $ open32 1 2
-- False
-- >>> contains 2 $ open32 1 2
-- False
--
open32 :: Float -> Float -> Interval Float
open32 x y = F32.shift 1 x ... F32.shift (-1) y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ open32L 1 2
-- False
-- >>> contains 2 $ open32L 1 2
-- True
--
open32L :: Float -> Float -> Interval Float
open32L x y = F32.shift 1 x ... y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ open32R 1 2
-- True
-- >>> contains 2 $ open32R 1 2
-- False
--
open32R :: Float -> Float -> Interval Float
open32R x y = x ... F32.shift (-1) y

-- | Construnct an open interval.
--
-- >>> contains 1 $ open64 1 2
-- False
-- >>> contains 2 $ open64 1 2
-- False
--
open64 :: Double -> Double -> Interval Double
open64 x y = F64.shift 1 x ... F64.shift (-1) y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ open64L 1 2
-- False
-- >>> contains 2 $ open64L 1 2
-- True
--
open64L :: Double -> Double -> Interval Double
open64L x y = F64.shift 1 x ... y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ open64R 1 2
-- True
-- >>> contains 2 $ open64R 1 2
-- False
--
open64R :: Double -> Double -> Interval Double
open64R x y = x ... F64.shift (-1) y

{-
-- | Generate a list of the contents on an interval.
--
-- Returns the list of values in the interval defined by a bounding pair.
--
-- Lawful variant of 'enumFromTo'.
--
indexFromTo :: Interval Float -> [Float]
indexFromTo i = case endpts i of
  Nothing -> []
  Just (x, y) -> flip unfoldr x $ \i -> if i ~~ y then Nothing else Just (i, shift 1 i)
-}

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Eq a => Eq (Interval a) where
  Empty == Empty = True
  Empty == _ = False
  _ == Empty = False
  I x y == I x' y' = x == x' && y == y'

-- | A < https://en.wikipedia.org/wiki/Containment_order containment order >
--
instance Preorder a => Preorder (Interval a) where
  Empty <~ _ = True
  _ <~ Empty = False
  I x y <~ I x' y' = x' <~ x && y <~ y'

{-
instance Lattice a => Lattice (Interval a) where
  (\/) = joinInterval
  (/\) = meetInterval

joinInterval Empty i = i
joinInterval i Empty = i
joinInterval (I x y) (I x' y') = I (x /\ x') (y \/ y')

instance Bounded a => Bounded (Interval a) where
  bottom = Empty
  top = bottom ... top
-}
