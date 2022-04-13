{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Ratio (
    -- * Rational
    ratw08,
    ratw16,
    ratw32,
    ratw64,
    ratwxx,
    ratnat,
    rati08,
    rati16,
    rati32,
    rati64,
    ratixx,
    ratint,
    ratrat,
    reduce,
    shiftr,
    Ratio (..),
) where

import Data.Bool
import Data.Connection.Cast hiding (ceiling, floor, lower)
import Data.Int
import Data.Order
import Data.Order.Syntax
import Data.Word
import GHC.Real (Ratio (..), Rational)
import Numeric.Natural
import Prelude hiding (Eq (..), Ord (..), until)

-- | A total version of 'GHC.Real.reduce'.
reduce :: Integral a => Ratio a -> Ratio a
reduce (x :% 0) = x :% 0
reduce (x :% y) = (x `quot` d) :% (y `quot` d) where d = gcd x y

-- | Shift by n 'units of least precision' where the ULP is determined by the denominator
--
-- This is an analog of 'Data.Connection.Float.shift32' for rationals.
shiftr :: Num a => a -> Ratio a -> Ratio a
shiftr n (x :% y) = (n + x) :% y

---------------------------------------------------------------------
-- Ratio Integer
---------------------------------------------------------------------

ratw08 :: Cast k Rational (Extended Word8)
ratw08 = ratext

ratw16 :: Cast k Rational (Extended Word16)
ratw16 = ratext

ratw32 :: Cast k Rational (Extended Word32)
ratw32 = ratext

ratw64 :: Cast k Rational (Extended Word64)
ratw64 = ratext

ratwxx :: Cast k Rational (Extended Word)
ratwxx = ratext

ratnat :: Cast k Rational (Extended Natural)
ratnat = Cast f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) (ceiling . max 0)

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x < 0) (~~ pinf) (floor . max 0)

rati08 :: Cast k Rational (Extended Int8)
rati08 = ratext

rati16 :: Cast k Rational (Extended Int16)
rati16 = ratext

rati32 :: Cast k Rational (Extended Int32)
rati32 = ratext

rati64 :: Cast k Rational (Extended Int64)
rati64 = ratext

ratixx :: Cast k Rational (Extended Int)
ratixx = ratext

ratint :: Cast k Rational (Extended Integer)
ratint = Cast f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) ceiling

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) floor

ratrat :: Cast k (Rational, Rational) Rational
ratrat = Cast f g h
  where
    -- join
    f (x, y) = maybe (1 / 0) (bool y x . (>= EQ)) (pcompare x y)

    g x = (x, x)

    -- meet
    h (x, y) = maybe (-1 / 0) (bool y x . (<= EQ)) (pcompare x y)

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

nan :: Num a => Ratio a
nan = 0 :% 0

ratext :: forall a k. (Bounded a, Integral a) => Cast k Rational (Extended a)
ratext = Cast f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x > high) $ \x -> if x < low then minBound else ceiling x

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x < low) (~~ pinf) $ \x -> if x > high then maxBound else floor x

    high = fromIntegral @a maxBound
    low = fromIntegral @a minBound

--low = -1 - high


{-
pabs :: (Lattice a, Eq a, Num a) => a -> a
pabs x = if 0 <~ x then x else negate x

cancel :: (Lattice a, Eq a, Num a) => Ratio a -> Ratio a
cancel (x :% y) = if x < 0 && y < 0 then (pabs x) :% (pabs y) else x :% y

-- | An exception-safe version of 'nanf' for rationals.
--
nanr :: Integral b => (a -> Ratio b) -> Maybe a -> Ratio b
nanr f = maybe (0 :% 0) f

-}
