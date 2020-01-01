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
  --, inti08
  -- * Int16
  , i16w16
  , i16w16'
  , i16i32
  , i16i64
  , i16int
  --, inti16
  -- * Int32
  , i32w32
  , i32w32'
  , i32i64
  , i32int
  --, inti32
  -- * Int64
  , i64w64
  , i64w64'
  , i64int
  --, inti64
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
import Data.Prd.Inf
import Data.Word
import Numeric.Natural
import qualified Control.Category as C


{-
class Prd a => ConnInt16 a where
  connInt16 :: Conn Int16 a

instance ConnInt16 Int16 where
  connInt16 = C.id

instance ConnInt16 Word16 where
  connInt16 = i16w16

instance ConnInt16 Int32 where
  connInt16 = i16i32

instance ConnInt16 Word32 where
  connInt16 = i16w16 >>> w16w32

instance ConnInt16 Int64 where
  connInt16 = i16i64

instance ConnInt16 Word64 where
  connInt16 = i16w16 >>> w16w64

class Prd a => ConnInt32 a where
  connInt32 :: Conn Int32 a

instance ConnInt32 Int32 where
  connInt32 = C.id

instance ConnInt32 Word32 where
  connInt32 = i32w32 

instance ConnInt32 Int64 where
  connInt32 = i32i64

instance ConnInt32 Word64 where
  connInt32 = i32w32 >>> w32w64

--TODO add more connections using Inf
-- Conn Integer Float
-- Conn Integer (Inf Int64)

class Prd a => ConnInteger a where
  connInteger :: Conn (Inf Integer) a

instance ConnInteger Integer where
  connInteger = C.id

instance ConnInteger Natural where
  connInteger = intnat

instance ConnInteger (Inf Int8) where
  connInteger = error "TODO"


-}



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

i08int :: Trip Int8 (Inf Integer)
i08int = Trip f (inf minimal g maximal) h where
  f i | i == minimal = Nnf
      | otherwise = Fin $ fromIntegral i

  g = fromInteger . min 127 . max (-128)

  h i | i == maximal = Pnf
      | otherwise = Fin $ fromIntegral i

i16w16 :: Conn Int16 Word16
i16w16 = unsigned

i16w16' :: Conn Int16 Word16
i16w16' = Conn (fromIntegral . max 0) (fromIntegral . min 32767) 

i16i32 :: Conn Int16 Int32
i16i32 = i16w16 >>> w16w32 >>> w32i32

i16i64 :: Conn Int16 Int64
i16i64 = i16w16 >>> w16w64 >>> w64i64

i16int :: Trip Int16 (Inf Integer)
i16int = Trip f (inf minimal g maximal) h where
  f i | i == minimal = Nnf
      | otherwise = Fin $ fromIntegral i

  g = fromInteger . min 32767 . max (-32768)

  h i | i == maximal = Pnf
      | otherwise = Fin $ fromIntegral i

i32w32 :: Conn Int32 Word32
i32w32 = unsigned

i32w32' :: Conn Int32 Word32
i32w32' = Conn (fromIntegral . max 0) (fromIntegral . min 2147483647)

i32i64 :: Conn Int32 Int64
i32i64 = i32w32 >>> w32w64 >>> w64i64

i32int :: Trip Int32 (Inf Integer)
i32int = Trip f (inf minimal g maximal) h where
  f i | i == minimal = Nnf
      | otherwise = Fin $ fromIntegral i

  g = fromInteger . min 2147483647 . max (-2147483648)

  h i | i == maximal = Pnf
      | otherwise = Fin $ fromIntegral i

i64w64 :: Conn Int64 Word64
i64w64 = unsigned

i64w64' :: Conn Int64 Word64
i64w64' = Conn (fromIntegral . max 0) (fromIntegral . min 9223372036854775807)

i64int :: Trip Int64 (Inf Integer)
i64int = Trip f (inf minimal g maximal) h where
  f i | i == minimal = Nnf
      | otherwise = Fin $ fromIntegral i

  g = fromInteger . min 9223372036854775807 . max (-9223372036854775808)

  h i | i == maximal = Pnf
      | otherwise = Fin $ fromIntegral i

ixxwxx :: Conn Int Word
ixxwxx = unsigned

intnat :: Conn Integer Natural
intnat = Conn (fromIntegral . max 0) fromIntegral

natint :: Conn Natural (Maybe Integer)
natint = Conn f (maybe minimal g) where
  f i | i == 0 = Nothing
      | otherwise = Just $ fromIntegral i

  g = fromInteger. max 0
