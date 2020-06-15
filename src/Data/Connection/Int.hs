{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Int (
  -- * Int8
    i08c08
  , i08w08
  , i08i16
  , i08i32
  , i08i64
  , i08int
  -- * Int16
  , i16c16
  , i16w16
  , i16i32
  , i16i64
  , i16int
  -- * Int32
  , i32c32
  , i32w32
  , i32i64
  , i32int
  -- * Int64
  , i64c64
  , i64w64
  , i64int
  -- * Int
  , ixxwxx
  , ixxi64
  , ixxint
  -- * Integer
  , intnat
  , natint
  ) where

import safe Control.Category ((>>>))
import safe Control.Applicative
import safe Control.Monad
import safe Data.Connection.Conn
import safe Data.Connection.Word
import safe Data.Int
import safe Data.Order.Syntax
import safe Data.Word
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Eq(..), Ord(..), Bounded)
import safe qualified Prelude as P

i08c08 :: ConnL Int8 CChar
i08c08 = ConnL CChar $ \(CChar x) -> x

i08w08 :: Conn k Int8 Word8
i08w08 = unsigned

i08int :: ConnL Int8 (Maybe Integer)
i08int = signed

i16c16 :: ConnL Int16 CShort
i16c16 = ConnL CShort $ \(CShort x) -> x

i16w16 :: Conn k Int16 Word16
i16w16 = unsigned

i16int :: ConnL Int16 (Maybe Integer)
i16int = signed

i32c32 :: ConnL Int32 CInt
i32c32 = ConnL CInt $ \(CInt x) -> x

i32w32 :: Conn k Int32 Word32
i32w32 = unsigned

i32int :: ConnL Int32 (Maybe Integer)
i32int = signed

i64c64 :: ConnL Int64 CLong
i64c64 = ConnL CLong $ \(CLong x) -> x

i64w64 :: Conn k Int64 Word64
i64w64 = unsigned

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxi64 :: Conn k Int Int64
ixxi64 = Conn fromIntegral fromIntegral fromIntegral

i64int :: ConnL Int64 (Maybe Integer)
i64int = signed

ixxwxx :: Conn k Int Word
ixxwxx = unsigned

-- | /Caution/: This assumes that 'Int' on your system is 64 bits.
ixxint :: ConnL Int (Maybe Integer)
ixxint = signed

intnat :: ConnL Integer Natural
intnat = ConnL (fromIntegral . max 0) fromIntegral

natint :: ConnL Natural (Maybe Integer)
natint = ConnL (fmap fromIntegral . fromPred (==0)) (maybe 0 $ P.fromInteger . max 0)

i08i16 :: ConnL Int8 Int16
i08i16 = i08w08 >>> w08w16 >>> w16i16

i08i32 :: ConnL Int8 Int32
i08i32 = i08w08 >>> w08w32 >>> w32i32

i08i64 :: ConnL Int8 Int64
i08i64 = i08w08 >>> w08w64 >>> w64i64

i16i32 :: ConnL Int16 Int32
i16i32 = i16w16 >>> w16w32 >>> w32i32

i16i64 :: ConnL Int16 Int64
i16i64 = i16w16 >>> w16w64 >>> w64i64

i32i64 :: ConnL Int32 Int64
i32i64 = i32w32 >>> w32w64 >>> w64i64

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------


fromPred :: Alternative f => (t -> Bool) -> t -> f t
fromPred p a = a <$ guard (p a)

unsigned :: (P.Bounded a, Integral a, Integral b) => Conn k a b
unsigned = Conn f g f where
  f y = fromIntegral (y + P.maxBound + 1)
  g x = fromIntegral x - P.minBound

signed :: forall a. (P.Bounded a, Integral a) => ConnL a (Maybe Integer)
signed = ConnL f g where
  f = fmap fromIntegral . fromPred (==P.minBound)
  g = maybe P.minBound $ P.fromInteger . min (fromIntegral @a P.maxBound) . max (fromIntegral @a P.minBound)

{-


clip08 :: Integer -> Integer
clip08 = min 127 . max (-128)

clip16 :: Integer -> Integer
clip16 = min 32767 . max (-32768)

clip32 :: Integer -> Integer
clip32 = min 2147483647 . max (-2147483648)

clip64 :: Integer -> Integer
clip64 = min 9223372036854775807 . max (-9223372036854775808)

unsigned :: (Bounded a, Preorder b, Integral a, Integral b) => ConnL a b
unsigned = ConnL f g where
  f = fromIntegral . max 0
  g = fromIntegral . min (f P.maxBound)

signed' :: forall a k. (Bounded a, Integral a) => Conn k a (Extended Integer)
signed' = Conn f g h where
  f = liftExtended (~~ P.minBound) (const False) fromIntegral
  g = extended P.minBound P.maxBound $ P.fromInteger . min (fromIntegral @a P.maxBound) . max (fromIntegral @a P.minBound)
  h = liftExtended (const False) (~~ P.maxBound) fromIntegral
-}


