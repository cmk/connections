module Data.Connection.Float where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Int
import Data.Prd.Nan
import Data.Word
import Data.Prd
import Data.Function (on)
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import GHC.Num (subtract)
import qualified Data.Bits as B
import qualified GHC.Float as F

import Prelude

newtype Ulp32 = Ulp32 { unUlp32 :: Int32 } deriving Show

ulp32Nan :: Ulp32 -> Bool
ulp32Nan (Ulp32 x) = x /= (min 2139095040 . max (- 2139095041)) x

instance Eq Ulp32 where
    x == y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (==) unUlp32 x y

instance Prd Ulp32 where
    x <~ y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<~) unUlp32 x y

instance Min Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Max Ulp32 where
    maximal = Ulp32 $ 2139095040

instance Bounded Ulp32 where
    minBound = minimal  
    maxBound = maximal

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulp32 . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulp32 Float
u32f32 = Conn (int32Float . unUlp32) (Ulp32 . floatInt32)

-- fromIntegral (maxBound :: Ulp32) + 1 , image of aNan

u32w64 :: Conn Ulp32 (Nan Word64)
u32w64 = Conn f g where
  conn = i32w32' >>> w32w64

  offset  = 2139095041 :: Word64
  offset' = 2139095041 :: Int32

  f x@(Ulp32 y) | ulp32Nan x = Nan
                | negative y = Def $ fromIntegral (y + offset')
                | otherwise = Def $ (fromIntegral y) + offset
               where fromIntegral = connl conn

  g x = case x of
          Nan -> Ulp32 offset'
          Def y | y < offset -> Ulp32 $ (fromIntegral y) - offset'
                | otherwise  -> Ulp32 $ fromIntegral ((min 4278190081 y) - offset)
               where fromIntegral = connr conn


--
--TODO handle neg case, get # of nans/denormals, collect constants         

abs' :: (Eq a, Bound a, Num a) => a -> a
abs' x = if x == minimal then abs (x+1) else abs x

f32i64 :: Conn Float (Nan Int64)
f32i64 = Conn (liftNan f) (nan (0/0) g) where
  f x | abs x <~ 2**24-1 = ceiling x
      | otherwise = if x >~ 0 then 2^24 else minimal

  g i | abs' i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**24
  
i64f32 :: Conn (Nan Int64) Float
i64f32 = Conn (nan (0/0) f) (liftNan g) where
  f i | abs i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**24 else -1/0

  g x | abs x <~ 2**24-1 = floor x
      | otherwise = if x >~ 0 then maximal else -2^24

f64i64 :: Conn Double (Nan Int64)
f64i64 = Conn (liftNan f) (nan (0/0) g) where
  f x | abs x <~ 2**53-1 = ceiling x
      | otherwise = if x >~ 0 then 2^53 else minimal

  g i | abs' i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**53
  
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nan (0/0) f) (liftNan g) where
  f i | abs i <~ 2^53-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**53 else -1/0

  g x | abs x <~ 2**53-1 = floor x
      | otherwise = if x >~ 0 then maximal else -2^53

float_word8 :: Trip Float (Nan Word8)
float_word8 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)

-- | Shift by /Int32/ units of least precision.
shift :: Int32 -> Float -> Float
shift n = int32Float . (+ n) . floatInt32

-- internal

-- Non-monotonic function 
signed32 :: Word32 -> Int32
signed32 x | x < 0x80000000 = fromIntegral x
           | otherwise      = fromIntegral (maximal - (x - 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x >= 0  = fromIntegral x
             | otherwise = 0x80000000 + (maximal - (fromIntegral x))

int32Float :: Int32 -> Float
int32Float = word32Float . unsigned32

floatInt32 :: Float -> Int32
floatInt32 = signed32 . floatWord32 

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- TODO force to positive representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32
