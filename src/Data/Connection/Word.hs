{-# LANGUAGE Safe #-}

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

import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Word
import safe Numeric.Natural

-- Word8
i08w08 :: ConnL Int8 Word8
i08w08 = unsigned

-- Word16
w08w16 :: ConnL Word8 Word16
w08w16 = unsigned

i08w16 :: ConnL Int8 Word16
i08w16 = unsigned

i16w16 :: ConnL Int16 Word16
i16w16 = unsigned

-- Word32
w08w32 :: ConnL Word8 Word32
w08w32 = unsigned

w16w32 :: ConnL Word16 Word32
w16w32 = unsigned

i08w32 :: ConnL Int8 Word32
i08w32 = unsigned

i16w32 :: ConnL Int16 Word32
i16w32 = unsigned

i32w32 :: ConnL Int32 Word32
i32w32 = unsigned

-- Word64
w08w64 :: ConnL Word8 Word64
w08w64 = unsigned

w16w64 :: ConnL Word16 Word64
w16w64 = unsigned

w32w64 :: ConnL Word32 Word64
w32w64 = unsigned

i08w64 :: ConnL Int8 Word64
i08w64 = unsigned

i16w64 :: ConnL Int16 Word64
i16w64 = unsigned

i32w64 :: ConnL Int32 Word64
i32w64 = unsigned

i64w64 :: ConnL Int64 Word64
i64w64 = unsigned

ixxw64 :: ConnL Int Word64
ixxw64 = unsigned

-- Word
w08wxx :: ConnL Word8 Word
w08wxx = unsigned

w16wxx :: ConnL Word16 Word
w16wxx = unsigned

w32wxx :: ConnL Word32 Word
w32wxx = unsigned

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
w64wxx :: Conn k Word64 Word
w64wxx = Conn fromIntegral fromIntegral fromIntegral

i08wxx :: ConnL Int8 Word
i08wxx = unsigned

i16wxx :: ConnL Int16 Word
i16wxx = unsigned

i32wxx :: ConnL Int32 Word
i32wxx = unsigned

i64wxx :: ConnL Int64 Word
i64wxx = unsigned

ixxwxx :: ConnL Int Word
ixxwxx = unsigned

-- Natural
w08nat :: ConnL Word8 Natural
w08nat = unsigned

w16nat :: ConnL Word16 Natural
w16nat = unsigned

w32nat :: ConnL Word32 Natural
w32nat = unsigned

w64nat :: ConnL Word64 Natural
w64nat = unsigned

wxxnat :: ConnL Word Natural
wxxnat = unsigned

i08nat :: ConnL Int8 Natural
i08nat = unsigned

i16nat :: ConnL Int16 Natural
i16nat = unsigned

i32nat :: ConnL Int32 Natural
i32nat = unsigned

i64nat :: ConnL Int64 Natural
i64nat = unsigned

ixxnat :: ConnL Int Natural
ixxnat = unsigned

intnat :: ConnL Integer Natural
intnat = ConnL (fromIntegral . max 0) fromIntegral

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

unsigned :: (Bounded a, Integral a, Integral b) => ConnL a b
unsigned = ConnL f g
  where
    f = fromIntegral . max 0
    g = fromIntegral . min (f maxBound)
