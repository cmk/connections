{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Time (
    -- * SystemTime
    sysixx,
    f32sys,
    f64sys,
    ratsys,
    f09sys,
    diffSystemTime,
    getSystemTime,
    SystemTime (..),
) where

import safe Data.Connection.Conn
import safe Data.Connection.Fixed
import safe Data.Connection.Ratio
import safe Data.Int
import safe Data.Order.Syntax
import safe Data.Time.Clock.System
import safe Prelude hiding (Eq (..), Ord (..), ceiling)

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Word

-- SystemTime

-------------------------

-- | The 'Int' is valued in seconds
sysixx :: Conn k SystemTime Int
sysixx = Conn f g h
  where
    f (normalize -> MkSystemTime s n) = fromIntegral s + if n == 0 then 0 else 1
    g i = MkSystemTime (fromIntegral i) 0
    h (normalize -> MkSystemTime s _) = fromIntegral s

-- | The 'Float' is valued in seconds.
--
-- >>> Data.Connection.ceiling f32sys (0/0)
-- PosInf
-- >>> Data.Connection.ceiling f32sys pi
-- Finite (MkSystemTime {systemSeconds = 3, systemNanoseconds = 141592742})
f32sys :: Conn 'L Float (Extended SystemTime)
f32sys = connL ratf32 >>> ratsys

-- | The 'Double' is valued in seconds.
--
-- >>> Data.Connection.ceiling f64sys (0/0)
-- PosInf
-- >>> Data.Connection.ceiling f64sys pi
-- Finite (MkSystemTime {systemSeconds = 3, systemNanoseconds = 141592654})
f64sys :: Conn 'L Double (Extended SystemTime)
f64sys = connL ratf64 >>> ratsys

-- | The 'Rational' is valued in seconds.
ratsys :: Conn k Rational (Extended SystemTime)
ratsys = ratfix >>> f09sys

-- | The 'Nano' is valued in seconds (to nanosecond precision).
f09sys :: Conn k (Extended Nano) (Extended SystemTime)
f09sys = Conn f g h
  where
    f NegInf = NegInf
    f (Finite i) = extend (const False) (> max64) (fromNanoSecs . clamp) i
    f PosInf = PosInf

    g = fmap toNanoSecs

    h NegInf = NegInf
    h (Finite i) = extend (< min64) (const False) (fromNanoSecs . clamp) i
    h PosInf = PosInf

    min64 = - 2 ^ 63
    max64 = 2 ^ 63 - 1

    clamp = max min64 . min max64

-- | Return the difference between two 'SystemTime's in seconds
--
-- >>> diffSystemTime (MkSystemTime 0 0) (MkSystemTime 0 maxBound)
-- -4.294967295
-- >>> divMod (maxBound @Word32) (10^9)
-- (4,294967295)
diffSystemTime :: SystemTime -> SystemTime -> Double
diffSystemTime x y = inner f64sys $ round2 ratsys (-) (Finite x) (Finite y)

-- Internal

-------------------------

s2ns :: Num a => a
s2ns = 10 ^ 9

toNanoSecs :: SystemTime -> Nano
toNanoSecs (MkSystemTime (toInteger -> s) (toInteger -> n)) = MkFixed (s * s2ns + n)

fromNanoSecs :: Nano -> SystemTime
fromNanoSecs (MkFixed i) = MkSystemTime (fromInteger $ q) (fromInteger r)
  where
    (q, r) = divMod i s2ns

normalize :: SystemTime -> SystemTime
normalize (MkSystemTime xs xn)
    | xn >= s2ns = MkSystemTime (xs + q) (fromIntegral r)
    | otherwise = MkSystemTime xs xn
  where
    (q, r) = fromIntegral xn `divMod` s2ns
