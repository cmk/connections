{-# Language Safe                #-}
module Data.Connection.Word (
  -- * Bool
    ordbin
  , binord
  , c08bin
  , binc08
  -- * Word8
  , w08c08
  , w08i08
  , w08w16
  , w08w32
  , w08w64
  , w08nat
  , w08nat'
  -- * Word16
  , w16c16
  , w16i16
  , w16w32
  , w16w64
  , w16nat
  , w16nat'
  -- * Word32
  , w32c32
  , w32i32
  , w32w64
  , w32nat
  , w32nat'
  -- * Word64
  , w64c64
  , w64i64
  , w64nat
  , w64nat'
  -- * Word
  , wxxnat
  , wxxnat'
) where

import safe Data.Connection.Type
import safe Data.Int
import safe Data.Order
import safe Data.Word
import safe Data.Lattice
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), Bounded)

ordbin :: Conn Ordering Bool
ordbin = Conn f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: Conn Bool Ordering
binord = Conn f g where
  f False = LT
  f _     = EQ

  g LT = False
  g _  = True

c08bin :: Conn CBool Bool
c08bin = Conn f g where
  f (CBool i) | i == 255 = True
              | otherwise = False
  
  g True = CBool 255
  g _ = CBool 254

binc08 :: Conn Bool CBool
binc08 = Conn f g where
  f False = CBool 0
  f _ = CBool 1

  g (CBool i) | i == 0 = False
              | otherwise = True

w08c08 :: Conn Word8 CUChar
w08c08 = Conn CUChar $ \(CUChar x) -> x

w08i08 :: Conn Word8 Int8
w08i08 = signed

w08nat :: Conn Word8 Natural
w08nat = unsigned

w08nat' :: Trip Word8 (Lowered Natural)
w08nat' = Trip (Left . fromIntegral)
               (lowered $ fromIntegral . min 255)
               (lowers fromIntegral)

w08w16 :: Conn Word8 Word16
w08w16 = unsigned

-- w08w32 = w08w16 >>> w16w32
w08w32 :: Conn Word8 Word32
w08w32 = unsigned

-- w08w64 = w08w32 >>> w32w64 = w08w16 >>> w16w64
w08w64 :: Conn Word8 Word64
w08w64 = unsigned

--w08nat :: Conn Word8 Natural
--w08nat = Conn fromIntegral (fromIntegral . min 255)

w16c16 :: Conn Word16 CUShort
w16c16 = Conn CUShort $ \(CUShort x) -> x

w16i16 :: Conn Word16 Int16
w16i16 = signed

w16w32 :: Conn Word16 Word32
w16w32 = unsigned

-- w16w64 = w16w32 >>> w32w64
w16w64 :: Conn Word16 Word64
w16w64 = unsigned

w16nat :: Conn Word16 Natural
w16nat = unsigned

w16nat' :: Trip Word16 (Lowered Natural)
w16nat' = Trip (Left . fromIntegral)
               (lowered $ fromIntegral . min 65535)
               (lowers fromIntegral)

w32c32 :: Conn Word32 CUInt
w32c32 = Conn CUInt $ \(CUInt x) -> x

w32i32 :: Conn Word32 Int32
w32i32 = signed

w32w64 :: Conn Word32 Word64
w32w64 = unsigned

w32nat :: Conn Word32 Natural
w32nat = unsigned

w32nat' :: Trip Word32 (Lowered Natural)
w32nat' = Trip (Left . fromIntegral)
               (lowered $ fromIntegral . min 4294967295)
               (lowers fromIntegral)

w64c64 :: Conn Word64 CULong
w64c64 = Conn CULong $ \(CULong x) -> x

w64i64 :: Conn Word64 Int64
w64i64 = signed

w64nat :: Conn Word64 Natural
w64nat = unsigned

w64nat' :: Trip Word64 (Lowered Natural)
w64nat' = Trip (Left . fromIntegral)
               (lowered $ fromIntegral . min 18446744073709551615)
               (lowers fromIntegral)

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
wxxnat :: Conn Word Natural
wxxnat = Conn fromIntegral (fromIntegral . min 18446744073709551615)

-- | /Caution/: This assumes that 'Word' on your system is 64 bits.
wxxnat' :: Trip Word (Lowered Natural)
wxxnat' = Trip (Left . fromIntegral)
               (lowered $ fromIntegral . min 18446744073709551615)
               (lowers fromIntegral)

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------
signed :: (Bounded b, Integral a, Integral b) => Conn a b
signed = Conn (\x -> fromIntegral x - bottom)
              (\y -> fromIntegral (y + top + 1))

unsigned :: (Bounded a, Integral a, Integral b) => Conn a b
unsigned = Conn f g where
  f = fromIntegral
  g = fromIntegral . min (f top)
