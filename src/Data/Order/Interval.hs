{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE Safe #-}

module Data.Order.Interval (
    Interval (),
    imap,
    (...),
    iempty,
    singleton,
    contains,
    endpts,
) where

import safe Data.Bifunctor (bimap)
import safe qualified Data.Eq as Eq
import safe Data.Order
import safe Data.Order.Syntax
import safe Prelude hiding (Bounded, Eq (..), Ord (..), until)

---------------------------------------------------------------------
-- Intervals
---------------------------------------------------------------------

-- | An interval in a poset /P/.
--
-- An interval in a poset /P/ is a subset /I/ of /P/ with the following property:
--
-- \( \forall x, y \in I, z \in P: x \leq z \leq y \Rightarrow z \in I \)
data Interval a = Empty | Interval !a !a deriving (Show)

-- | Map over an interval.
--
-- /Note/ this is not a functor, as a non-monotonic map
-- may cause the interval to collapse to the iempty interval.
imap :: Preorder b => (a -> b) -> Interval a -> Interval b
imap f = maybe iempty (uncurry (...)) . fmap (bimap f f) . endpts

infix 3 ...

-- | Construct an interval from a pair of points.
--
-- /Note/: Endpoints are preorder-sorted. If /pcompare x y = Nothing/
-- then the resulting interval will be empty.
(...) :: Preorder a => a -> a -> Interval a
x ... y = case pcompare x y of
    Just LT -> Interval x y
    Just EQ -> Interval x y
    _ -> Empty
{-# INLINE (...) #-}

-- | The iempty interval.
--
-- >>> iempty
-- Empty
iempty :: Interval a
iempty = Empty
{-# INLINE iempty #-}

-- | Construct an interval containing a single point.
--
-- >>> singleton 1
-- 1 ... 1
singleton :: a -> Interval a
singleton a = Interval a a
{-# INLINE singleton #-}

-- | Obtain the endpoints of an interval.
endpts :: Interval a -> Maybe (a, a)
endpts Empty = Nothing
endpts (Interval x y) = Just (x, y)
{-# INLINE endpts #-}

contains :: Preorder a => Interval a -> a -> Bool
contains Empty _ = False
contains (Interval x y) p = x <~ p && p <~ y

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Eq a => Eq (Interval a) where
    Empty == Empty = True
    Empty == _ = False
    _ == Empty = False
    Interval x y == Interval x' y' = x == x' && y == y'

-- | A < https://en.wikipedia.org/wiki/Containment_order containment order >
instance Preorder a => Preorder (Interval a) where
    Empty <~ _ = True
    _ <~ Empty = False
    Interval x y <~ Interval x' y' = x' <~ x && y <~ y'

{-
instance Bounded 'L a => Connection k (Maybe a) (Interval a) where
  conn = Conn f g h where
    f = maybe iempty singleton
    g = maybe Nothing (Just . uncurry (\/)) . endpts
    h = maybe iempty $ \x -> minimal ... x

instance Lattice a => Connection k (Interval a) (Maybe a) where
  conn = Conn f g h where
    f = maybe Nothing (Just . uncurry (\/)) . endpts
    g = maybe iempty singleton
    h = maybe Nothing (Just . uncurry (/\)) . endpts

instance Lattice a => Lattice (Interval a) where
  (\/) = joinInterval
  (/\) = meetInterval

bottom = Empty
top = bottom ... top
joinInterval Empty i = i
joinInterval i Empty = i
joinInterval (I x y) (I x' y') = I (x /\ x') (y \/ y')

-}
