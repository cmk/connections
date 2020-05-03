{-# Language ConstraintKinds #-}
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
  , i08int
  -- * Int16
  , i16w16
  , i16w16'
  , i16i32
  , i16i64
  , i16int
  -- * Int32
  , i32w32
  , i32w32'
  , i32i64
  , i32int
  -- * Int64
  , i64w64
  , i64w64'
  , i64int
  -- * Int
  , ixxint
  , ixxwxx
  -- * Integer
  , intnat
  , natint
  ) where

import Control.Category ((>>>))
import Data.Connection.Conn
import Data.Connection.Word
import Data.Connection.Trip
import Data.Int
import Data.Prd
import Data.Prd.Top
import Data.Word
import Numeric.Natural

import Prelude hiding (Bounded, fromInteger)
import qualified Prelude as P

--class Prd a => ConnInteger a where
--  inttyp :: Conn (Bound Integer) a

{-
-- TODO: add Ord-based Prd instances, test
-- 
--i08chr :: Conn Int8 Char
i08c08 :: Conn Int8 CChar
w08u08 :: Conn Word8 UChar
i16c16 :: Conn Int16 CShort
w16u16 :: Conn Word16 CUShort
i32c32 :: Conn Int32 CInt
w32u32 :: Conn Word32 CUInt
i64c64 :: Conn Int64 CLong
w64u64 :: Conn Word64 CULong
w64csz :: Conn Word64 CSize

f32c32 :: Conn Float CFloat
f64c64 :: Conn Double CDouble

-- | Lawful replacement for the version in base.
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = connl connection . Just . Fin

-}


unsigned :: (Bounded a, Integral a, Integral b) => Conn a b
unsigned = Conn (\y -> fromIntegral (y P.+ maximal P.+ 1))
                (\x -> fromIntegral x P.- minimal) 

i08w08' :: Conn Int8 Word8
i08w08' = unsigned

i08w08 :: Conn Int8 Word8
i08w08 = Conn (fromIntegral . max 0) (fromIntegral . min 127)

i08i16 :: Conn Int8 Int16
i08i16 = i08w08' >>> w08w16 >>> w16i16

i08i32 :: Conn Int8 Int32
i08i32 = i08w08' >>> w08w32 >>> w32i32

i08i64 :: Conn Int8 Int64
i08i64 = i08w08' >>> w08w64 >>> w64i64

i08int :: Trip Int8 (Bound Integer)
i08int = Trip (liftBottom' fromIntegral)
              (bounded $ P.fromInteger . min 127 . max (-128))
              (liftTop' fromIntegral)

i16w16' :: Conn Int16 Word16
i16w16' = unsigned

i16w16 :: Conn Int16 Word16
i16w16 = Conn (fromIntegral . max 0) (fromIntegral . min 32767) 

i16i32 :: Conn Int16 Int32
i16i32 = i16w16' >>> w16w32 >>> w32i32

i16i64 :: Conn Int16 Int64
i16i64 = i16w16' >>> w16w64 >>> w64i64

i16int :: Trip Int16 (Bound Integer)
i16int = Trip (liftBottom' fromIntegral)
              (bounded $ P.fromInteger . min 32767 . max (-32768))
              (liftTop' fromIntegral)

i32w32' :: Conn Int32 Word32
i32w32' = unsigned

i32w32 :: Conn Int32 Word32
i32w32 = Conn (fromIntegral . max 0) (fromIntegral . min 2147483647)

i32i64 :: Conn Int32 Int64
i32i64 = i32w32' >>> w32w64 >>> w64i64

i32int :: Trip Int32 (Bound Integer)
i32int = Trip (liftBottom' fromIntegral)
              (bounded $ P.fromInteger . min 2147483647 . max (-2147483648))
              (liftTop' fromIntegral)

i64w64' :: Conn Int64 Word64
i64w64' = unsigned

i64w64 :: Conn Int64 Word64
i64w64 = Conn (fromIntegral . max 0) (fromIntegral . min 9223372036854775807)

i64int :: Trip Int64 (Bound Integer)
i64int = Trip (liftBottom' fromIntegral)
              (bounded $ P.fromInteger . min 9223372036854775807 . max (-9223372036854775808))
              (liftTop' fromIntegral)

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxint :: Trip Int (Bound Integer)
ixxint = Trip (liftBottom' fromIntegral)
              (bounded $ P.fromInteger . min 9223372036854775807 . max (-9223372036854775808))
              (liftTop' fromIntegral)

ixxwxx :: Conn Int Word
ixxwxx = unsigned

intnat :: Conn Integer Natural
intnat = Conn (fromIntegral . max 0) fromIntegral

natint :: Conn Natural (Maybe Integer)
natint = Conn f (maybe minimal g) where
  f i | i == 0 = Nothing
      | otherwise = Just $ fromIntegral i

  g = P.fromInteger . max 0

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------
{-
instance ConnInteger Int8 where
  inttyp = tripr i08int

instance ConnInteger Int16 where
  inttyp = tripr i16int

instance ConnInteger Int32 where
  inttyp = tripr i32int

instance ConnInteger Int64 where
  inttyp = tripr i64int

instance ConnInteger Int where
  inttyp = tripr ixxint

instance ConnInteger Word8 where
  inttyp = tripr i08int >>> i08w08

instance ConnInteger Word16 where
  inttyp = tripr i16int >>> i16w16

instance ConnInteger Word32 where
  inttyp = tripr i32int >>> i32w32

instance ConnInteger Word64 where
  inttyp = tripr i64int >>> i64w64

instance ConnInteger Word where
  inttyp = tripr ixxint >>> ixxwxx
-}
