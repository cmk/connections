{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Ratio (
    Ratio (..),
    reduce,
    shiftr,

    -- * Rational
    rati08,
    rati16,
    rati32,
    rati64,
    ratixx,
    ratint,
    ratfix,
    ratf32,
    ratf64,

    -- * Positive
    posw08,
    posw16,
    posw32,
    posw64,
    poswxx,
    posnat,
) where

import safe Data.Connection.Conn
import safe Data.Connection.Fixed
import safe Data.Connection.Float as Float
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
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

rati08 :: Conn k Rational (Extended Int8)
rati08 = tripleI

rati16 :: Conn k Rational (Extended Int16)
rati16 = tripleI

rati32 :: Conn k Rational (Extended Int32)
rati32 = tripleI

rati64 :: Conn k Rational (Extended Int64)
rati64 = tripleI

ratixx :: Conn k Rational (Extended Int)
ratixx = tripleI

ratint :: Conn k Rational (Extended Integer)
ratint = Conn f g h
  where
    f = liftExtended (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) ceiling

    g = extended ninf pinf fromIntegral

    h = liftExtended (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) floor

ratfix :: forall e k. HasResolution e => Conn k Rational (Fixed e)
ratfix = Conn f g h
  where
    prec = resolution (Proxy :: Proxy e)

    f (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ let i = n `div` d in if n `mod` d == 0 then i else i + 1

    g = toRational

    h (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ n `div` d

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

---------------------------------------------------------------------
-- Ratio Natural
---------------------------------------------------------------------

posw08 :: Conn k Positive (Lowered Word8)
posw08 = tripleW

posw16 :: Conn k Positive (Lowered Word16)
posw16 = tripleW

posw32 :: Conn k Positive (Lowered Word32)
posw32 = tripleW

posw64 :: Conn k Positive (Lowered Word64)
posw64 = tripleW

poswxx :: Conn k Positive (Lowered Word)
poswxx = tripleW

posnat :: Conn k Positive (Lowered Natural)
posnat = Conn f g h
  where
    f = liftEitherR (\x -> x ~~ nan || x ~~ pinf) ceiling

    g = either fromIntegral (const pinf)

    h = liftEitherR (~~ pinf) $ \x -> if x ~~ nan then 0 else floor x

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

pinf :: Num a => Ratio a
pinf = 1 :% 0

ninf :: Num a => Ratio a
ninf = (-1) :% 0

nan :: Num a => Ratio a
nan = 0 :% 0

tripleW :: forall a k. (Bounded a, Integral a) => Conn k Positive (Lowered a)
tripleW = Conn f g h
  where
    f x
        | x ~~ nan = Right maxBound
        | x > high = Right maxBound
        | otherwise = Left $ ceiling x

    g = either fromIntegral (const pinf)

    h x
        | x ~~ nan = Left minBound
        | x ~~ pinf = Right maxBound
        | x > high = Left maxBound
        | otherwise = Left $ floor x

    high = fromIntegral @a maxBound

tripleI :: forall a k. (Bounded a, Integral a) => Conn k Rational (Extended a)
tripleI = Conn f g h
  where
    f = liftExtended (~~ ninf) (\x -> x ~~ nan || x > high) $ \x -> if x < low then minBound else ceiling x

    g = extended ninf pinf fromIntegral

    h = liftExtended (\x -> x ~~ nan || x < low) (~~ pinf) $ \x -> if x > high then maxBound else floor x

    high = fromIntegral @a maxBound
    low = -1 - high

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

ratpos :: Conn k Rational Positive
ratpos = Conn k f g h where

  f = liftExtended (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) ceiling

  g = extended minBound maxBound fromIntegral

  h = liftExtended (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) floor
-}
