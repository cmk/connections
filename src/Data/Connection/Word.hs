
{-# LANGUAGE DataKinds #-}

module Data.Connection.Word (
    -- * Bool
    bndbin,

    -- * Word8
    i08w08,

    -- * Word16
    w08w16,
    i08w16,
    i16w16,

    -- * Word32
    w08w32,
    w16w32,
    i08w32,
    i16w32,
    i32w32,

    -- * Word64
    w08w64,
    w16w64,
    w32w64,
    wxxw64,
    i08w64,
    i16w64,
    i32w64,
    i64w64,
    ixxw64,

    -- * Word
    w08wxx,
    w16wxx,
    w32wxx,
    w64wxx,
    i08wxx,
    i16wxx,
    i32wxx,
    i64wxx,
    ixxwxx,

    -- * Natural
    w08nat,
    w16nat,
    w32nat,
    w64nat,
    wxxnat,
    i08nat,
    i16nat,
    i32nat,
    i64nat,
    ixxnat,
    intnat,
) where

import Data.Connection.Cast
import Data.Int
import Data.Word
import Numeric.Natural

{-# INLINEABLE bndbin #-}
bndbin :: (Eq a, Bounded a) => Cast k a Bool
bndbin = Cast f g h
  where
    f i
        | i == minBound = False
        | otherwise = True

    g x = if x then maxBound else minBound

    h i
        | i == maxBound = True
        | otherwise = False

-- Word8
i08w08 :: Cast 'L Int8 Word8
i08w08 = conn

-- Word16
w08w16 :: Cast 'L Word8 Word16
w08w16 = conn

i08w16 :: Cast 'L Int8 Word16
i08w16 = conn

i16w16 :: Cast 'L Int16 Word16
i16w16 = conn

-- Word32
w08w32 :: Cast 'L Word8 Word32
w08w32 = conn

w16w32 :: Cast 'L Word16 Word32
w16w32 = conn

i08w32 :: Cast 'L Int8 Word32
i08w32 = conn

i16w32 :: Cast 'L Int16 Word32
i16w32 = conn

i32w32 :: Cast 'L Int32 Word32
i32w32 = conn

-- Word64
w08w64 :: Cast 'L Word8 Word64
w08w64 = conn

w16w64 :: Cast 'L Word16 Word64
w16w64 = conn

w32w64 :: Cast 'L Word32 Word64
w32w64 = conn

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
wxxw64 :: Cast k Word Word64
wxxw64 = Cast fromIntegral fromIntegral fromIntegral

i08w64 :: Cast 'L Int8 Word64
i08w64 = conn

i16w64 :: Cast 'L Int16 Word64
i16w64 = conn

i32w64 :: Cast 'L Int32 Word64
i32w64 = conn

i64w64 :: Cast 'L Int64 Word64
i64w64 = conn

ixxw64 :: Cast 'L Int Word64
ixxw64 = conn

-- Word
w08wxx :: Cast 'L Word8 Word
w08wxx = conn

w16wxx :: Cast 'L Word16 Word
w16wxx = conn

w32wxx :: Cast 'L Word32 Word
w32wxx = conn

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
w64wxx :: Cast k Word64 Word
w64wxx = Cast fromIntegral fromIntegral fromIntegral

i08wxx :: Cast 'L Int8 Word
i08wxx = conn

i16wxx :: Cast 'L Int16 Word
i16wxx = conn

i32wxx :: Cast 'L Int32 Word
i32wxx = conn

i64wxx :: Cast 'L Int64 Word
i64wxx = conn

ixxwxx :: Cast 'L Int Word
ixxwxx = conn

-- Natural
w08nat :: Cast 'L Word8 Natural
w08nat = conn

w16nat :: Cast 'L Word16 Natural
w16nat = conn

w32nat :: Cast 'L Word32 Natural
w32nat = conn

w64nat :: Cast 'L Word64 Natural
w64nat = conn

wxxnat :: Cast 'L Word Natural
wxxnat = conn

i08nat :: Cast 'L Int8 Natural
i08nat = conn

i16nat :: Cast 'L Int16 Natural
i16nat = conn

i32nat :: Cast 'L Int32 Natural
i32nat = conn

i64nat :: Cast 'L Int64 Natural
i64nat = conn

ixxnat :: Cast 'L Int Natural
ixxnat = conn

intnat :: Cast 'L Integer Natural
intnat = CastL (fromIntegral . max 0) fromIntegral

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-# INLINE conn #-}
conn :: (Bounded a, Integral a, Integral b) => Cast 'L a b
conn = CastL f g
  where
    f = fromIntegral . max 0
    g = fromIntegral . min (f maxBound)
