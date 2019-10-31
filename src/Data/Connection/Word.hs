module Data.Connection.Word (
  -- * Word8
    w08i08
  , w08w16
  , w08w32
  , w08w64
  , w08nat
  -- * Word16
  , w16i16
  , w16w32
  , w16w64
  , w16nat
  -- * Word32
  , w32i32
  , w32w64
  , w32nat
  -- * Word64
  , w64i64
  , w64nat
) where

import Control.Category ((>>>))
import Data.Connection
import Data.Int
import Data.Prd
import Data.Word

import Numeric.Natural

signed :: (Bounded b, Integral a, Integral b) => Conn a b
signed = 
  Conn (\x -> fromIntegral x - minBound) (\y -> fromIntegral (y + maxBound + 1))

w08i08 :: Conn Word8 Int8
w08i08 = signed

w08w16 :: Conn Word8 Word16
w08w16 = Conn fromIntegral (fromIntegral . min 255)

-- w08w32 = w08w16 >>> w16w32
w08w32 :: Conn Word8 Word32
w08w32 = Conn fromIntegral (fromIntegral . min 255)

-- w08w64 = w08w32 >>> w32w64 = w08w16 >>> w16w64
w08w64 :: Conn Word8 Word64
w08w64 = Conn fromIntegral (fromIntegral . min 255)

w08nat :: Conn Word8 Natural
w08nat = Conn fromIntegral (fromIntegral . min 255)

w16i16 :: Conn Word16 Int16
w16i16 = signed

w16w32 :: Conn Word16 Word32
w16w32 = Conn fromIntegral (fromIntegral . min 65535)

-- w16w64 = w16w32 >>> w32w64
w16w64 :: Conn Word16 Word64
w16w64 = Conn fromIntegral (fromIntegral . min 65535)

w16nat :: Conn Word16 Natural
w16nat = Conn fromIntegral (fromIntegral . min 65535)

w32i32 :: Conn Word32 Int32
w32i32 = signed

w32w64 :: Conn Word32 Word64
w32w64 = Conn fromIntegral (fromIntegral . min 4294967295)

w32nat :: Conn Word32 Natural
w32nat = Conn fromIntegral (fromIntegral . min 4294967295)

w64i64 :: Conn Word64 Int64
w64i64 = signed

w64nat :: Conn Word64 Natural
w64nat = Conn fromIntegral (fromIntegral . min 18446744073709551615)
