{-# Language Safe                #-}
module Data.Connection.Word (
  -- * Bool
    c08bin
  , binc08
  -- * Word8
  , w08c08
  , w08i08
  , w08w16
  , w08w32
  , w08w64
  , w08wxx
  , w08nat
  -- * Word16
  , w16c16
  , w16i16
  , w16w32
  , w16w64
  , w16wxx
  , w16nat
  -- * Word32
  , w32c32
  , w32i32
  , w32w64
  , w32wxx
  , w32nat
  -- * Word64
  , w64c64
  , w64i64
  , w64nat
  -- * Word
  , wxxw64
  , wxxnat
) where

import safe Data.Connection.Conn
import safe Data.Int
import safe Data.Order
import safe Data.Order.Syntax
import safe Data.Order.Extended
import safe Data.Word
import safe Data.Lattice
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), Eq(..), Bounded)

c08bin :: ConnL CBool Bool
c08bin = ConnL f g where
  f (CBool i) | i == 255 = True
              | otherwise = False
  
  g True = CBool 255
  g _ = CBool 254

binc08 :: ConnL Bool CBool
binc08 = ConnL f g where
  f False = CBool 0
  f _ = CBool 1

  g (CBool i) | i == 0 = False
              | otherwise = True

w08c08 :: ConnL Word8 CUChar
w08c08 = ConnL CUChar $ \(CUChar x) -> x

w08i08 :: ConnL Word8 Int8
w08i08 = signed

w08nat :: ConnL Word8 Natural
w08nat = unsigned

w08w16 :: ConnL Word8 Word16
w08w16 = unsigned

-- w08w32 = w08w16 >>> w16w32
w08w32 :: ConnL Word8 Word32
w08w32 = unsigned

-- w08w64 = w08w32 >>> w32w64 = w08w16 >>> w16w64
w08w64 :: ConnL Word8 Word64
w08w64 = unsigned

w08wxx :: ConnL Word8 Word
w08wxx = unsigned

w16c16 :: ConnL Word16 CUShort
w16c16 = ConnL CUShort $ \(CUShort x) -> x

w16i16 :: ConnL Word16 Int16
w16i16 = signed

w16w32 :: ConnL Word16 Word32
w16w32 = unsigned

-- w16w64 = w16w32 >>> w32w64
w16w64 :: ConnL Word16 Word64
w16w64 = unsigned

w16wxx :: ConnL Word16 Word
w16wxx = unsigned

w16nat :: ConnL Word16 Natural
w16nat = unsigned

w32c32 :: ConnL Word32 CUInt
w32c32 = ConnL CUInt $ \(CUInt x) -> x

w32i32 :: ConnL Word32 Int32
w32i32 = signed

w32w64 :: ConnL Word32 Word64
w32w64 = unsigned

w32wxx :: ConnL Word32 Word
w32wxx = unsigned

w32nat :: ConnL Word32 Natural
w32nat = unsigned

w64c64 :: ConnL Word64 CULong
w64c64 = ConnL CULong $ \(CULong x) -> x

w64i64 :: ConnL Word64 Int64
w64i64 = signed

w64nat :: ConnL Word64 Natural
w64nat = unsigned

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
wxxw64 :: Conn k Word Word64
wxxw64 = Conn fromIntegral fromIntegral fromIntegral

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
wxxnat :: ConnL Word Natural
wxxnat = ConnL fromIntegral (fromIntegral . min 18446744073709551615)

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------
signed :: (Bounded b, Integral a, Integral b) => ConnL a b
signed = ConnL (\x -> fromIntegral x - bottom)
               (\y -> fromIntegral (y + top + 1))

unsigned :: (Bounded a, Preorder b, Integral a, Integral b) => ConnL a b
unsigned = ConnL f g where
  f = fromIntegral
  g = fromIntegral . min (f top)
