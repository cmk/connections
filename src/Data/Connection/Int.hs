{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Connection.Int (
    -- * Int16
    w08i16,
    i08i16,

    -- * Int32
    w08i32,
    w16i32,
    i08i32,
    i16i32,

    -- * Int64
    w08i64,
    w16i64,
    w32i64,
    i08i64,
    i16i64,
    i32i64,

    -- * Int
    w08ixx,
    w16ixx,
    w32ixx,
    i08ixx,
    i16ixx,
    i32ixx,
    i64ixx,

    -- * Integer
    w08int,
    w16int,
    w32int,
    w64int,
    wxxint,
    natint,
    i08int,
    i16int,
    i32int,
    i64int,
    ixxint,
) where

import safe Control.Applicative
import safe Control.Monad
import safe Data.Connection.Cast
import safe Data.Int
import safe Data.Word
import safe Numeric.Natural
import safe Prelude

-- Int16
w08i16 :: Cast 'L Word8 (Maybe Int16)
w08i16 = signed

i08i16 :: Cast 'L Int8 (Maybe Int16)
i08i16 = signed

-- Int32
w08i32 :: Cast 'L Word8 (Maybe Int32)
w08i32 = signed

w16i32 :: Cast 'L Word16 (Maybe Int32)
w16i32 = signed

i08i32 :: Cast 'L Int8 (Maybe Int32)
i08i32 = signed

i16i32 :: Cast 'L Int16 (Maybe Int32)
i16i32 = signed

-- Int64
w08i64 :: Cast 'L Word8 (Maybe Int64)
w08i64 = signed

w16i64 :: Cast 'L Word16 (Maybe Int64)
w16i64 = signed

w32i64 :: Cast 'L Word32 (Maybe Int64)
w32i64 = signed

i08i64 :: Cast 'L Int8 (Maybe Int64)
i08i64 = signed

i16i64 :: Cast 'L Int16 (Maybe Int64)
i16i64 = signed

i32i64 :: Cast 'L Int32 (Maybe Int64)
i32i64 = signed

-- Int
w08ixx :: Cast 'L Word8 (Maybe Int)
w08ixx = signed

w16ixx :: Cast 'L Word16 (Maybe Int)
w16ixx = signed

w32ixx :: Cast 'L Word32 (Maybe Int)
w32ixx = signed

i08ixx :: Cast 'L Int8 (Maybe Int)
i08ixx = signed

i16ixx :: Cast 'L Int16 (Maybe Int)
i16ixx = signed

i32ixx :: Cast 'L Int32 (Maybe Int)
i32ixx = signed

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
i64ixx :: Cast k Int64 Int
i64ixx = Cast fromIntegral fromIntegral fromIntegral

-- Integer
w08int :: Cast 'L Word8 (Maybe Integer)
w08int = signed

w16int :: Cast 'L Word16 (Maybe Integer)
w16int = signed

w32int :: Cast 'L Word32 (Maybe Integer)
w32int = signed

w64int :: Cast 'L Word64 (Maybe Integer)
w64int = signed

wxxint :: Cast 'L Word (Maybe Integer)
wxxint = signed

natint :: Cast 'L Natural (Maybe Integer)
natint = CastL (fmap fromIntegral . fromPred (/= 0)) (maybe 0 $ fromInteger . max 0)

i08int :: Cast 'L Int8 (Maybe Integer)
i08int = signed

i16int :: Cast 'L Int16 (Maybe Integer)
i16int = signed

i32int :: Cast 'L Int32 (Maybe Integer)
i32int = signed

i64int :: Cast 'L Int64 (Maybe Integer)
i64int = signed

ixxint :: Cast 'L Int (Maybe Integer)
ixxint = signed

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

fromPred :: (a -> Bool) -> a -> Maybe a
fromPred p a = a <$ guard (p a)

signed :: forall a b. (Bounded a, Integral a, Integral b) => Cast 'L a (Maybe b)
signed = CastL f g
  where
    f = fmap fromIntegral . fromPred (/= minBound)
    g = maybe minBound $ fromIntegral @b . min (fromIntegral @a maxBound) . max (fromIntegral @a minBound)
