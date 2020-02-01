-- Note that in most cases the obvious implementation is not a valid
-- Galois connection. For example:
--
-- @
-- i08i16  = Conn fromIntegral (fromIntegral . min 127 . max (-1208))
-- @
--
module Data.Connection.Int (
    ConnInteger(..)
  , fromInteger
  -- * Int8
  , i08w08
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
  , ixxwxx
  -- * Integer
  , intnat
  , natint
  ) where

import Control.Category ((>>>))
import Data.Connection
import Data.Connection.Word
import Data.Int
import Data.Prd
import Data.Prd.Nan
import Data.Semiring
import Data.Semilattice.Bounded
import Data.Word
import Numeric.Natural
import qualified Control.Category as C

import Prelude hiding (Num(..), (^), Bounded)
import qualified Prelude as P

class Prd a => ConnInteger a where
  connInteger :: Conn (Bounded Integer) a

instance ConnInteger Int8 where
  connInteger = tripr i08int

instance ConnInteger Int16 where
  connInteger = tripr i16int

instance ConnInteger Int32 where
  connInteger = tripr i32int

instance ConnInteger Int64 where
  connInteger = tripr i64int

instance ConnInteger Word8 where
  connInteger = tripr i08int >>> i08w08

instance ConnInteger Word16 where
  connInteger = tripr i16int >>> i16w16

instance ConnInteger Word32 where
  connInteger = tripr i32int >>> i32w32

instance ConnInteger Word64 where
  connInteger = tripr i64int >>> i64w64

-- | Lawful replacement for the version in base.
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = connl connInteger . Just . Finite

unsigned :: (Bound a, Integral a, Integral b) => Conn a b
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

i08int :: Trip Int8 (Bounded Integer)
i08int = Trip (liftBottom' fromIntegral)
              (bounded' $ P.fromInteger . min 127 . max (-128))
              (liftTop' fromIntegral)

i16w16' :: Conn Int16 Word16
i16w16' = unsigned

i16w16 :: Conn Int16 Word16
i16w16 = Conn (fromIntegral . max 0) (fromIntegral . min 32767) 

i16i32 :: Conn Int16 Int32
i16i32 = i16w16' >>> w16w32 >>> w32i32

i16i64 :: Conn Int16 Int64
i16i64 = i16w16' >>> w16w64 >>> w64i64

i16int :: Trip Int16 (Bounded Integer)
i16int = Trip (liftBottom' fromIntegral)
              (bounded' $ P.fromInteger . min 32767 . max (-32768))
              (liftTop' fromIntegral)

i32w32' :: Conn Int32 Word32
i32w32' = unsigned

i32w32 :: Conn Int32 Word32
i32w32 = Conn (fromIntegral . max 0) (fromIntegral . min 2147483647)

i32i64 :: Conn Int32 Int64
i32i64 = i32w32' >>> w32w64 >>> w64i64

i32int :: Trip Int32 (Bounded Integer)
i32int = Trip (liftBottom' fromIntegral)
              (bounded' $ P.fromInteger . min 2147483647 . max (-2147483648))
              (liftTop' fromIntegral)

i64w64' :: Conn Int64 Word64
i64w64' = unsigned

i64w64 :: Conn Int64 Word64
i64w64 = Conn (fromIntegral . max 0) (fromIntegral . min 9223372036854775807)

i64int :: Trip Int64 (Bounded Integer)
i64int = Trip (liftBottom' fromIntegral)
              (bounded' $ P.fromInteger . min 9223372036854775807 . max (-9223372036854775808))
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
