-- Note that in most cases the obvious implementation is not a valid
-- Galois connection. For example:
--
-- @
-- i08i16  = Conn fromIntegral (fromIntegral . min 127 . max (-1208))
-- @
--
module Data.Connection.Int (
  -- * Int8
    i08w08
  , i08w08'
  , i08i16
  , i08i32
  , i08i64
  -- * Int16
  , i16w16
  , i16w16'
  , i16i32
  , i16i64
  -- * Int32
  , i32w32
  , i32w32'
  , i32i64
  -- * Int64
  , i64w64
  , i64w64'
  -- * Integer
  , intnat
  ) where

import Control.Category ((>>>))
import Data.Connection
import Data.Connection.Word
import Data.Int
import Data.Prd
import Data.Word

import Numeric.Natural

unsigned :: (Bounded a, Integral a, Integral b) => Conn a b
unsigned = Conn (\y -> fromIntegral (y + maxBound + 1))
                (\x -> fromIntegral x - minBound) 

i08w08 :: Conn Int8 Word8
i08w08 = unsigned

i08w08' :: Conn Int8 Word8
i08w08' = Conn (fromIntegral . max 0) (fromIntegral . min 127)

i08i16 :: Conn Int8 Int16
i08i16 = i08w08 >>> w08w16 >>> w16i16

i08i32 :: Conn Int8 Int32
i08i32 = i08w08 >>> w08w32 >>> w32i32

i08i64 :: Conn Int8 Int64
i08i64 = i08w08 >>> w08w64 >>> w64i64

i16w16 :: Conn Int16 Word16
i16w16 = unsigned

i16w16' :: Conn Int16 Word16
i16w16' = Conn (fromIntegral . max 0) (fromIntegral . min 32767) 

i16i32 :: Conn Int16 Int32
i16i32 = i16w16 >>> w16w32 >>> w32i32

i16i64 :: Conn Int16 Int64
i16i64 = i16w16 >>> w16w64 >>> w64i64

i32w32 :: Conn Int32 Word32
i32w32 = unsigned

i32w32' :: Conn Int32 Word32
i32w32' = Conn (fromIntegral . max 0) (fromIntegral . min 2147483647)

i32i64 :: Conn Int32 Int64
i32i64 = i32w32 >>> w32w64 >>> w64i64

i64w64 :: Conn Int64 Word64
i64w64 = unsigned

i64w64' :: Conn Int64 Word64
i64w64' = Conn (fromIntegral . max 0) (fromIntegral . min 9223372036854775807)

intnat :: Conn Integer Natural
intnat = Conn (fromIntegral . max 0) fromIntegral
