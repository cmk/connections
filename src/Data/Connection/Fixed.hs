{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Safe #-}

module Data.Connection.Fixed (
    
    -- * Uni
    Uni,
    f00int,

    -- * Deci
    Deci,
    f01f00,

    -- * Centi
    Centi,
    f02f00,
    f02f01,

    -- * Milli
    Milli,
    f03f00,
    f03f01,
    f03f02,

    -- * Micro
    Micro,
    f06f00,
    f06f01,
    f06f02,
    f06f03,

    -- * Nano
    Nano,
    f09f00,
    f09f01,
    f09f02,
    f09f03,
    f09f06,

    -- * Pico
    Pico,
    f12f00,
    f12f01,
    f12f02,
    f12f03,
    f12f06,
    f12f09,

    -- * Fixed
    f32fix,
    f64fix,
    ratfix,
    shiftf,
    showFixed,
    Fixed (..),
    HasResolution (..),
) where

import safe Data.Connection.Conn
import safe Data.Connection.Ratio
import safe Data.Fixed
import safe Data.Order
import safe Data.Order.Syntax
import safe Data.Proxy
import safe GHC.Real (Ratio (..), Rational)
import safe Prelude hiding (Eq (..), Ord (..))

-- | Shift by n 'units of least precision' where the ULP is determined by the precision.
--
-- This is an analog of 'Data.Connection.Float.shift32' for fixed point numbers.
shiftf :: Integer -> Fixed a -> Fixed a
shiftf j (MkFixed i) = MkFixed (i + j)

-- Uni

f00int :: Conn k Uni Integer
f00int = Conn f g f
  where
    f (MkFixed i) = i
    g = fromInteger

-- Deci

f01f00 :: Conn k Deci Uni
f01f00 = fixfix 10

-- Centi

f02f00 :: Conn k Centi Uni
f02f00 = fixfix 100

f02f01 :: Conn k Centi Deci
f02f01 = fixfix 10

-- Milli

f03f00 :: Conn k Milli Uni
f03f00 = fixfix 1000

f03f01 :: Conn k Milli Deci
f03f01 = fixfix 100

f03f02 :: Conn k Milli Centi
f03f02 = fixfix 10

-- Micro

f06f00 :: Conn k Micro Uni
f06f00 = fixfix $ 10 ^ (6 :: Integer)

f06f01 :: Conn k Micro Deci
f06f01 = fixfix $ 10 ^ (5 :: Integer)

f06f02 :: Conn k Micro Centi
f06f02 = fixfix $ 10 ^ (4 :: Integer)

f06f03 :: Conn k Micro Milli
f06f03 = fixfix $ 10 ^ (3 :: Integer)

-- Nano

f09f00 :: Conn k Nano Uni
f09f00 = fixfix $ 10 ^ (9 :: Integer)

f09f01 :: Conn k Nano Deci
f09f01 = fixfix $ 10 ^ (8 :: Integer)

f09f02 :: Conn k Nano Centi
f09f02 = fixfix $ 10 ^ (7 :: Integer)

f09f03 :: Conn k Nano Milli
f09f03 = fixfix $ 10 ^ (6 :: Integer)

f09f06 :: Conn k Nano Micro
f09f06 = fixfix $ 10 ^ (3 :: Integer)

-- Pico

f12f00 :: Conn k Pico Uni
f12f00 = fixfix $ 10 ^ (12 :: Integer)

f12f01 :: Conn k Pico Deci
f12f01 = fixfix $ 10 ^ (11 :: Integer)

f12f02 :: Conn k Pico Centi
f12f02 = fixfix $ 10 ^ (10 :: Integer)

f12f03 :: Conn k Pico Milli
f12f03 = fixfix $ 10 ^ (9 :: Integer)

f12f06 :: Conn k Pico Micro
f12f06 = fixfix $ 10 ^ (6 :: Integer)

f12f09 :: Conn k Pico Nano
f12f09 = fixfix $ 10 ^ (3 :: Integer)

-- Fixed

f32fix :: HasResolution e => Conn 'L Float (Extended (Fixed e))
f32fix = connL ratf32 >>> ratfix

f64fix :: HasResolution e => Conn 'L Double (Extended (Fixed e))
f64fix = connL ratf64 >>> ratfix

ratfix :: forall e k. HasResolution e => Conn k Rational (Extended (Fixed e))
ratfix = Conn f' g h'
  where
    prec = resolution (Proxy :: Proxy e)

    f (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ let i = n `div` d in if n `mod` d == 0 then i else i + 1

    f' = extend (~~ ninf) (\x -> x ~~ nan || x ~~ pinf) f

    g = extended ninf pinf toRational

    h (reduce . (* (toRational prec)) -> n :% d) = MkFixed $ n `div` d

    h' = extend (\x -> x ~~ nan || x ~~ ninf) (~~ pinf) h

    pinf = 1 :% 0

    ninf = (-1) :% 0

    nan = 0 :% 0


-- Internal

-------------------------

fixfix :: Integer -> Conn k (Fixed e1) (Fixed e2)
fixfix prec = Conn f g h
  where
    f (MkFixed i) = MkFixed $ let j = i `div` prec in if i `mod` prec == 0 then j else j + 1
    g (MkFixed i) = MkFixed $ i * prec
    h (MkFixed i) = MkFixed $ let j = i `div` prec in if i `mod` prec == 0 then j else j -1
