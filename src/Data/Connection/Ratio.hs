{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE Safe #-}
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
    ratfix,
    ratf32,
    ratf64,
    ratrat,
    reduce,
    shiftr,
    Ratio (..),
) where

import safe Data.Bool
import safe Data.Connection.Conn hiding (ceiling, floor, lower)
import safe Data.Connection.Fixed
import safe Data.Connection.Float as Float
import safe Data.Int
import safe Data.Order
import safe Data.Order.Syntax
import safe Data.Proxy
import safe Data.Ratio
import safe Data.Word
import safe GHC.Real (Ratio (..), Rational)
import safe Numeric.Natural
import safe Prelude hiding (Eq (..), Ord (..), until)

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

ratw08 :: Conn k Rational (Extended Word8)
ratw08 = ratext

ratw16 :: Conn k Rational (Extended Word16)
ratw16 = ratext

ratw32 :: Conn k Rational (Extended Word32)
ratw32 = ratext

ratw64 :: Conn k Rational (Extended Word64)
ratw64 = ratext

ratwxx :: Conn k Rational (Extended Word)
ratwxx = ratext

ratnat :: Conn k Rational (Extended Natural)
ratnat = Conn f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) (ceiling . max 0)

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x < 0) (~~ pinf) (floor . max 0)

rati08 :: Conn k Rational (Extended Int8)
rati08 = ratext

rati16 :: Conn k Rational (Extended Int16)
rati16 = ratext

rati32 :: Conn k Rational (Extended Int32)
rati32 = ratext

rati64 :: Conn k Rational (Extended Int64)
rati64 = ratext

ratixx :: Conn k Rational (Extended Int)
ratixx = ratext

ratint :: Conn k Rational (Extended Integer)
ratint = Conn f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) ceiling

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) floor

ratfix :: forall e k. HasResolution e => Conn k Rational (Extended (Fixed e))
ratfix = Conn f' g h'
  where
    prec = resolution (Proxy :: Proxy e)

    f (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ let i = n `div` d in if n `mod` d == 0 then i else i + 1

    f' = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) f

    g = extended ninf pinf toRational

    h (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ n `div` d

    h' = extend (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) h

ratf32 :: Conn k Rational Float
ratf32 = Conn (toFractional f) (fromFractional g) (toFractional h)
  where
    f x =
        let est = fromRational x
         in if fromFractional g est >~ x
                then est
                else ascendf est (fromFractional g) x

    g = flip approxRational 0

    h x =
        let est = fromRational x
         in if fromFractional g est <~ x
                then est
                else descendf est (fromFractional g) x

    ascendf z g1 y = Float.until (\x -> g1 x >~ y) (<~) (Float.shift32 1) z

    descendf z f1 x = Float.until (\y -> f1 y <~ x) (>~) (Float.shift32 (-1)) z

ratf64 :: Conn k Rational Double
ratf64 = Conn (toFractional f) (fromFractional g) (toFractional h)
  where
    f x =
        let est = fromRational x
         in if fromFractional g est >~ x
                then est
                else ascendf est (fromFractional g) x

    g = flip approxRational 0

    h x =
        let est = fromRational x
         in if fromFractional g est <~ x
                then est
                else descendf est (fromFractional g) x

    ascendf z g1 y = Float.until (\x -> g1 x >~ y) (<~) (Float.shift64 1) z

    descendf z f1 x = Float.until (\y -> f1 y <~ x) (>~) (Float.shift64 (-1)) z

ratrat :: Conn k (Rational, Rational) Rational
ratrat = Conn f g h
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

ratext :: forall a k. (Bounded a, Integral a) => Conn k Rational (Extended a)
ratext = Conn f g h
  where
    f = extend (~~ ninf) (\x -> x ~~ nan || x > high) $ \x -> if x < low then minBound else ceiling x

    g = extended ninf pinf fromIntegral

    h = extend (\x -> x ~~ nan || x < low) (~~ pinf) $ \x -> if x > high then maxBound else floor x

    high = fromIntegral @a maxBound
    low = fromIntegral @a minBound

--low = -1 - high

toFractional :: Fractional a => (Rational -> a) -> Rational -> a
toFractional f x
    | x ~~ nan = 0 / 0
    | x ~~ ninf = (-1) / 0
    | x ~~ pinf = 1 / 0
    | otherwise = f x

fromFractional :: (Order a, Fractional a) => (a -> Rational) -> a -> Rational
fromFractional f x
    | x ~~ 0 / 0 = nan
    | x ~~ (-1) / 0 = ninf
    | x ~~ 1 / 0 = pinf
    | otherwise = f x

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
