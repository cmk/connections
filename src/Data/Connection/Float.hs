module Data.Connection.Float (
  -- * Float
    TripFloat(..)
  , fromFloat
  , f32i08
  , f32i16
  , f32i32
  , i32f32
  -- * Double
  , TripDouble(..)
  , fromDouble
  , f64i08
  , f64i16
  , f64i32
  , f64i64
  , i64f64
) where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import Data.Float
import Data.Function (on)
import Data.Int
import Data.Prd
import Data.Prd.Nan
import Data.Ratio
import Data.Semifield hiding (fin)
import Data.Semilattice
import Data.Semilattice.Bounded
import Data.Semiring
import Data.Word
import GHC.Num (subtract)
import GHC.Real hiding ((^),(/))
import Prelude as P hiding (Ord(..), Num(..), Fractional(..), (^), Bounded)
import qualified Control.Category as C
import qualified Data.Bits as B
import qualified GHC.Float as F
import qualified GHC.Float.RealFracMethods as R


class Prd a => TripFloat a where
  tripFloat :: Trip Float a

class Prd a => TripDouble a where
  tripDouble :: Trip Double a

fromFloat :: TripFloat a => Float -> a
fromFloat = connl . tripl $ tripFloat

fromDouble :: TripDouble a => Double -> a
fromDouble = connl . tripl $ tripDouble

-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Float'.
f32i16 :: Trip Float (Extended Int16)
f32i16 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: Conn Float (Nan Int32)
f32i32 = Conn (liftNan f) (nan' g) where
  f x | abs x <= 2**24-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^24 else minimal

  g i | abs' i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nan' g) (liftNan f) where
  f x | abs x <= 2**24-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^24

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -1/0

-- | All 'Int8' values are exactly representable in a 'Double'.
f64i08 :: Trip Double (Extended Int8)
f64i08 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Double'.
f64i16 :: Trip Double (Extended Int16)
f64i16 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | All 'Int32' values are exactly representable in a 'Double'.
f64i32 :: Trip Double (Extended Int32)
f64i32 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ ninf = Nothing
      | x < imin = fin bottom
      | otherwise = fin $ P.ceiling x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Just Top
      | x > imax = fin top
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 2147483647 

  imin = -2147483648

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Nan Int64)
f64i64 = Conn (liftNan f) (nan' g) where
  f x | abs x <= 2**53-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^53 else minimal

  g i | abs' i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nan' g) (liftNan f) where
  f x | abs x <= 2**53-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^53

  g i | abs i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**53 else -1/0

abs' x = if x == minimal then abs (x+one) else abs x

{- slightly broken
f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)
-}

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance TripFloat Float where
  tripFloat = C.id

instance TripFloat (Nan Ordering) where
  tripFloat = fldord

instance TripFloat (Extended Int8) where
  tripFloat = f32i08

instance TripFloat (Extended Int16) where
  tripFloat = f32i16

--instance TripFloat Ulp32 where
--  tripFloat = f32u32

--instance TripFloat (Nan Word8) where
--  tripFloat = tripl f32w08

instance TripDouble Double where
  tripDouble = C.id

instance TripDouble (Nan Ordering) where
  tripDouble = fldord

--instance TripDouble Ulp64 where
--  tripDouble = f64u64

instance TripDouble (Extended Int8) where
  tripDouble = f64i08

instance TripDouble (Extended Int16) where
  tripDouble = f64i16

instance TripDouble (Extended Int32) where
  tripDouble = f64i32

