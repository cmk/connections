{-# LANGUAGE Safe                       #-}

module Data.Order.Total (
  -- * Total orders
    TotalOrder
  , min ,max
  , compare
  , comparing
  -- * DerivingVia
  , Total(..) 
  -- * Re-exports
  , Ord.Ord()
) where

import safe Control.Exception
import safe Data.Order
import safe qualified Data.Ord as Ord

import Prelude hiding (Ord(..))

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

-- | 
-- > comparing p x y = compare (p x) (p y)
--
-- Useful combinator for use in conjunction with the @xxxBy@ family
-- of functions from "Data.List", for example:
--
-- >   ... sortBy (comparing fst) ...
comparing :: TotalOrder a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)
