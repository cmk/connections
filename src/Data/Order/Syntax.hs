{-# LANGUAGE Safe #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Utilities for custom preludes and RebindableSyntax.
module Data.Order.Syntax (
  -- * Partial orders
    PartialOrder
  , (==),(/=)
  , (<=),(>=)
  -- * Total orders
  , TotalOrder
  , min ,max
  , compare
  , comparing
  -- * Re-exports
  , Eq.Eq()
  , Ord.Ord()
) where

import safe Control.Exception
import safe Data.Order
import safe qualified Data.Eq as Eq
import safe qualified Data.Ord as Ord

import Prelude hiding (Eq(..),Ord(..))

-------------------------------------------------------------------------------
-- Partial orders
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Partially_ordered_set partial order > on /a/.
--
-- Note: ideally this would be a subclass of /Preorder/.
--
-- We instead use a constraint kind in order to retain compatibility with the
-- downstream users of /Eq/.
-- 
type PartialOrder a = (Eq.Eq a, Preorder a)

infix 4 ==, /=, <=, >=

-- | A wrapper around /==/ that forces /NaN == NaN/.
--
(==) :: Eq.Eq a => a -> a -> Bool
(==) x y = if x Eq./= x && y Eq./= y then True else x Eq.== y

(/=) :: Eq.Eq a => a -> a -> Bool
(/=) x y = not (x == y)

(<=) :: PartialOrder a => a -> a -> Bool
(<=) x y = x < y || x == y

(>=) :: PartialOrder a => a -> a -> Bool
(>=) x y = x > y || x == y

-------------------------------------------------------------------------------
-- Total orders
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Total_order total order > on /a/.
-- 
-- Note: ideally this would be a subclass of /PartialOrder/, without instances
-- for /Float/, /Double/, /Rational/, etc.
--
-- We instead use a constraint kind in order to retain compatibility with the
-- downstream users of /Ord/.
-- 
type TotalOrder a = (Ord.Ord a, Preorder a)

infix 4 `min`, `max`, `compare`, `comparing`

-- | Find the minimum of two values.
--
-- > min x y == if x <= y then x else y = True
--
-- /Note/: this function will throw a /ArithException/ on floats and rationals
-- if one of the arguments is finite and the other is /NaN/.
--
min :: TotalOrder a => a -> a -> a
min x y = case compare x y of
  GT -> y
  _  -> x

-- | Find the minimum of two values.
--
-- > max x y == if x >= y then x else y = True
--
-- /Note/: this function will throw a /ArithException/ on floats and rationals
-- if one of the arguments is finite and the other is /NaN/.
--
max :: TotalOrder a => a -> a -> a
max x y = case compare x y of
  LT -> y
  _  -> x

-- | Compare two values in a total order.
--
-- > x < y = compare x y == LT
-- > x > y = compare x y == GT
-- > x == y = compare x y == EQ
--
-- >>> compare (1/0 :: Double) 0
-- GT
-- >>> compare (-1/0 :: Double) 0
-- LT
-- >>> compare (1/0 :: Double) (0/0)
-- GT
-- >>> compare (-1/0 :: Double) (0/0)
-- LT
--
-- /Note/: this function will throw a /ArithException/ on floats and rationals
-- if one of the arguments is finite and the other is /NaN/:
--
-- >>> compare (0/0 :: Double) 0
-- *** Exception: divide by zero
--
compare :: TotalOrder a => a -> a -> Ordering
compare x y = case pcompare x y of
  Just o -> o
  Nothing -> throw DivideByZero

-- | Compare on the range of a function.
--
-- > comparing p x y = compare (p x) (p y)
--
comparing :: TotalOrder a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)
