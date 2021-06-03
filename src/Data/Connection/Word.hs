{-# LANGUAGE Safe #-}
{-# LANGUAGE DataKinds #-}

module Data.Connection.Word (
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

import safe Data.Connection.Cast
import safe Data.Int
import safe Data.Word
import safe Numeric.Natural

-- Word8
i08w08 :: Cast 'L Int8 Word8
i08w08 = unsigned

-- Word16
w08w16 :: Cast 'L Word8 Word16
w08w16 = unsigned

i08w16 :: Cast 'L Int8 Word16
i08w16 = unsigned

i16w16 :: Cast 'L Int16 Word16
i16w16 = unsigned

-- Word32
w08w32 :: Cast 'L Word8 Word32
w08w32 = unsigned

w16w32 :: Cast 'L Word16 Word32
w16w32 = unsigned

i08w32 :: Cast 'L Int8 Word32
i08w32 = unsigned

i16w32 :: Cast 'L Int16 Word32
i16w32 = unsigned

i32w32 :: Cast 'L Int32 Word32
i32w32 = unsigned

-- Word64
w08w64 :: Cast 'L Word8 Word64
w08w64 = unsigned

w16w64 :: Cast 'L Word16 Word64
w16w64 = unsigned

w32w64 :: Cast 'L Word32 Word64
w32w64 = unsigned

i08w64 :: Cast 'L Int8 Word64
i08w64 = unsigned

i16w64 :: Cast 'L Int16 Word64
i16w64 = unsigned

i32w64 :: Cast 'L Int32 Word64
i32w64 = unsigned

i64w64 :: Cast 'L Int64 Word64
i64w64 = unsigned

ixxw64 :: Cast 'L Int Word64
ixxw64 = unsigned

-- Word
w08wxx :: Cast 'L Word8 Word
w08wxx = unsigned

w16wxx :: Cast 'L Word16 Word
w16wxx = unsigned

w32wxx :: Cast 'L Word32 Word
w32wxx = unsigned

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
w64wxx :: Cast k Word64 Word
w64wxx = Cast fromIntegral fromIntegral fromIntegral

i08wxx :: Cast 'L Int8 Word
i08wxx = unsigned

i16wxx :: Cast 'L Int16 Word
i16wxx = unsigned

i32wxx :: Cast 'L Int32 Word
i32wxx = unsigned

i64wxx :: Cast 'L Int64 Word
i64wxx = unsigned

ixxwxx :: Cast 'L Int Word
ixxwxx = unsigned

-- Natural
w08nat :: Cast 'L Word8 Natural
w08nat = unsigned

w16nat :: Cast 'L Word16 Natural
w16nat = unsigned

w32nat :: Cast 'L Word32 Natural
w32nat = unsigned

w64nat :: Cast 'L Word64 Natural
w64nat = unsigned

wxxnat :: Cast 'L Word Natural
wxxnat = unsigned

i08nat :: Cast 'L Int8 Natural
i08nat = unsigned

i16nat :: Cast 'L Int16 Natural
i16nat = unsigned

i32nat :: Cast 'L Int32 Natural
i32nat = unsigned

i64nat :: Cast 'L Int64 Natural
i64nat = unsigned

ixxnat :: Cast 'L Int Natural
ixxnat = unsigned

intnat :: Cast 'L Integer Natural
intnat = CastL (fromIntegral . max 0) fromIntegral

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

unsigned :: (Bounded a, Integral a, Integral b) => Cast 'L a b
unsigned = CastL f g
  where
    f = fromIntegral . max 0
    g = fromIntegral . min (f maxBound)
