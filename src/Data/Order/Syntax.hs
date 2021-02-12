{-# LANGUAGE Safe #-}
{-# LANGUAGE ConstraintKinds #-}
-- | Utilities for custom preludes and RebindableSyntax.
module Data.Order.Syntax (
  -- * Preorders
    (<), (>)
  -- * Partial orders
  , Order
  , (==),(/=)
  , (<=),(>=)
  -- * Total orders
  , Total
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

infix 4 <, >

-- | A strict preorder relation on /a/.
--
-- Is /x/ less than /y/?
--
-- '<' is irreflexive, asymmetric, and transitive.
--
-- > x < y = x <~ y && not (y <~ x)
-- > x < y = maybe False (< EQ) (pcompare x y)
--
-- When '<~' is antisymmetric then /a/ is a partial 
-- order and we have:
-- 
-- > x < y = x <~ y && x /~ y
--
-- for all /x/, /y/ in /a/.
--
(<) :: Preorder a => a -> a -> Bool
(<) = plt

-- | A converse strict preorder relation on /a/.
--
-- Is /x/ greater than /y/?
--
-- '>' is irreflexive, asymmetric, and transitive.
--
-- > x > y = x >~ y && not (y >~ x)
-- > x > y = maybe False (> EQ) (pcompare x y)
-- 
-- When '<~' is antisymmetric then /a/ is a partial 
-- order and we have:
-- 
-- > x > y = x >~ y && x /~ y
--
-- for all /x/, /y/ in /a/.
--
(>) :: Preorder a => a -> a -> Bool
(>) = flip (<)

-------------------------------------------------------------------------------
-- Partial orders
-------------------------------------------------------------------------------


infix 4 ==, /=, <=, >=

-- | A wrapper around /==/ that forces /NaN == NaN/.
--
(==) :: Eq.Eq a => a -> a -> Bool
(==) x y = if x Eq./= x && y Eq./= y then True else x Eq.== y

(/=) :: Eq.Eq a => a -> a -> Bool
(/=) x y = not (x == y)

(<=) :: Order a => a -> a -> Bool
(<=) x y = x < y || x == y

(>=) :: Order a => a -> a -> Bool
(>=) x y = x > y || x == y

-------------------------------------------------------------------------------
-- Total orders
-------------------------------------------------------------------------------


infix 4 `min`, `max`, `compare`, `comparing`

-- | Find the minimum of two values.
--
-- > min x y == if x <= y then x else y = True
--
-- /Note/: this function will throw a /ArithException/ on floats and rationals
-- if one of the arguments is finite and the other is /NaN/.
--
min :: Total a => a -> a -> a
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
max :: Total a => a -> a -> a
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
compare :: Total a => a -> a -> Ordering
compare x y = case pcompare x y of
  Just o -> o
  Nothing -> throw DivideByZero

-- | Compare on the range of a function.
--
-- > comparing p x y = compare (p x) (p y)
--
comparing :: Total a => (b -> a) -> b -> b -> Ordering
comparing p x y = compare (p x) (p y)
