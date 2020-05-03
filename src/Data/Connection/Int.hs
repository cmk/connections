{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Int (
  -- * Int8
    i08c08
  , i08w08
  , i08w08'
  , i08int
  , i08int'
  -- * Int16
  , i16c16
  , i16w16
  , i16w16'
  , i16int
  , i16int'
  -- * Int32
  , i32c32
  , i32w32
  , i32w32'
  , i32int
  , i32int'
  -- * Int64
  , i64c64
  , i64w64
  , i64w64'
  , i64int
  , i64int'
  -- * Int
  , ixxwxx
  , ixxwxx'
  , ixxint
  , ixxint'
  -- * Integer
  , intnat
  , natint
  ) where

import safe Control.Category ((>>>))
import safe Data.Connection.Conn
import safe Data.Connection.Word
import safe Data.Connection.Trip
import safe Data.Int
import safe Data.Prd
import safe Data.Prd.Top
import safe Data.Word
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Bounded, fromInteger)
import safe qualified Prelude as P

i08c08 :: Conn Int8 CChar
i08c08 = Conn CChar $ \(CChar x) -> x

i08w08 :: Conn Int8 Word8
i08w08 = unsigned -- Conn (fromIntegral . max 0) (fromIntegral . min 127)

i08w08' :: Trip Int8 Word8
i08w08' = unsigned'

i08int :: Conn Int8 (Maybe Integer)
i08int = signed -- Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . clip08)

i08int' :: Trip Int8 (Bound Integer)
i08int' = signed'

i16c16 :: Conn Int16 CShort
i16c16 = Conn CShort $ \(CShort x) -> x

i16w16 :: Conn Int16 Word16
i16w16 = unsigned -- Conn (fromIntegral . max 0) (fromIntegral . min 32767) 

i16w16' :: Trip Int16 Word16
i16w16' = unsigned'

i16int :: Conn Int16 (Maybe Integer)
i16int = signed -- Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . clip16)

i16int' :: Trip Int16 (Bound Integer)
i16int' = signed'

i32c32 :: Conn Int32 CInt
i32c32 = Conn CInt $ \(CInt x) -> x

i32w32 :: Conn Int32 Word32
i32w32 = unsigned -- Conn (fromIntegral . max 0) (fromIntegral . min 2147483647)

i32w32' :: Trip Int32 Word32
i32w32' = unsigned'

i32int :: Conn Int32 (Maybe Integer)
i32int = signed -- Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . clip32)

i32int' :: Trip Int32 (Bound Integer)
i32int' = signed'

i64c64 :: Conn Int64 CLong
i64c64 = Conn CLong $ \(CLong x) -> x

i64w64 :: Conn Int64 Word64
i64w64 = unsigned -- Conn (fromIntegral . max 0) (fromIntegral . min 9223372036854775807)

i64w64' :: Trip Int64 Word64
i64w64' = unsigned'

i64int :: Conn Int64 (Maybe Integer)
i64int = signed -- Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . clip64)

i64int' :: Trip Int64 (Bound Integer)
i64int' = signed'

ixxwxx :: Conn Int Word
ixxwxx = unsigned

ixxwxx' :: Trip Int Word
ixxwxx' = unsigned'

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxint :: Conn Int (Maybe Integer)
ixxint = signed -- Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . clip64)

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxint' :: Trip Int (Bound Integer)
ixxint' = signed'

intnat :: Conn Integer Natural
intnat = Conn (fromIntegral . max 0) fromIntegral

natint :: Conn Natural (Maybe Integer)
natint = Conn (liftBottom P.fromIntegral) (maybe minimal $ P.fromInteger . max 0)

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------


{-
i08i16 :: Conn Int8 Int16
i08i16 = i08w08' >>> w08w16 >>> w16i16

i08i32 :: Conn Int8 Int32
i08i32 = i08w08' >>> w08w32 >>> w32i32

i08i64 :: Conn Int8 Int64
i08i64 = i08w08' >>> w08w64 >>> w64i64

i16i32 :: Conn Int16 Int32
i16i32 = i16w16' >>> w16w32 >>> w32i32

i16i64 :: Conn Int16 Int64
i16i64 = i16w16' >>> w16w64 >>> w64i64

i32i64 :: Conn Int32 Int64
i32i64 = i32w32' >>> w32w64 >>> w64i64

clip08 :: Integer -> Integer
clip08 = min 127 . max (-128)

clip16 :: Integer -> Integer
clip16 = min 32767 . max (-32768)

clip32 :: Integer -> Integer
clip32 = min 2147483647 . max (-2147483648)

clip64 :: Integer -> Integer
clip64 = min 9223372036854775807 . max (-9223372036854775808)
-}


signed :: (Bounded a, Integral a) => Conn a (Bottom Integer)
signed = Conn (liftBottom f) g where
  f = fromIntegral
  g = maybe minimal $ P.fromInteger . min (f maximal) . max (f minimal)

signed' :: (Bounded a, Integral a) => Trip a (Bound Integer)
signed' = Trip (liftBottom' f) g (liftTop' f) where
  f = fromIntegral
  g = bounded $ P.fromInteger . min (f maximal) . max (f minimal)

unsigned :: (Maximal a, Integral a, Integral b) => Conn a b
unsigned = Conn f g where
  f = fromIntegral . max 0
  g = fromIntegral . min (f maximal)

unsigned' :: (Bounded a, Integral a, Integral b) => Trip a b
unsigned' = Trip f g f where
  f y = fromIntegral (y + maximal + 1)
  g x = fromIntegral x - minimal
