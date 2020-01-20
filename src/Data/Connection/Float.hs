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
import qualified GHC.Float.RealFracMethods as R

import Prelude
import qualified Control.Category as C

import Data.Ratio

import GHC.Real

class Prd a => ConnRational a where
  connRational :: Conn Rational a

fromRational :: ConnRational a => Rational -> a
fromRational = connl connRational

instance ConnRational Rational where
  connRational = C.id

instance ConnRational Float where
  connRational = tripl ratf32

class Prd a => ConnFloat a where
  connFloat :: Conn Float a

instance ConnFloat Float where
  connFloat = C.id

instance ConnFloat Ulp32 where
  connFloat = f32u32

instance ConnFloat (Nan Int32) where
  connFloat = f32i32

--instance ConnFloat (Nan Word8) where
--  connFloat = tripl f32w08



class Prd a => ConnDouble a where
  connDouble :: Conn Double a

instance ConnDouble Double where
  connDouble = C.id

--instance ConnDouble Ulp64 where
--  connDouble = f64u64

instance ConnDouble (Nan Int64) where
  connDouble = f64i64

-- | 32 bit unit of least precision type.
--
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

instance Minimal Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Maximal Ulp32 where
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

{-

--TODO check these 4 probably buggy
f32ixx :: Trip Float (Nan (Inf Int))
f32ixx = Trip
  (liftNan f)
  (nan (0/0) $ g)
  (liftNan h)
  where
    f x | not (finite x) && signBit x = minimal
        | not (finite x) && not (signBit x) = maximal
        | otherwise = R.celingFloatInt x

    g = F.int2Float

    h x | not (finite x) && signBit x = minimal
        | not (finite x) && not (signBit x) = maximal
        | otherwise = R.floorFloatInt x

f64ixx :: Trip Double (Nan Int)
f64ixx = Trip
  (liftNan R.ceilingDoubleInt)
  (nan (0/0) $ F.int2Double)
  (liftNan R.floorDoubleInt)

-}


-- >>> ceiling' f32int (0/0)
-- Nan
-- >>> ceiling' f32int 0.1
-- Def 1
-- >>> ceiling' f32int 0.9
-- Def 1
-- >>> ceiling' f32int 1.1
-- Def 2
-- >>> ceiling' f32int (-1.1)
-- Def (-1)
--
{- slightly broken
f32int :: Trip Float (Nan Integer)
f32int = Trip
  (liftNan R.ceilingFloatInteger)
  (nan (0/0) $ flip F.rationalToFloat 1) -- TODO map large / small ints to Inf / NInf
  (liftNan R.floorFloatInteger)

f64int :: Trip Double (Nan Integer)
f64int = Trip
  (liftNan R.ceilingDoubleInteger)
  (nan (0/0) $ flip F.rationalToDouble 1)
  (liftNan R.floorDoubleInteger)

f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)
-}


--fldord :: (Field a, Prd a) => Trip a (Nan Ordering)
f32ord :: Trip Float (Nan Ordering)
f32ord = Trip f g h where

  g (Def GT) = 1/0
  g (Def LT) = - 1/0
  g (Def EQ) = 0
  g Nan = 0/0
  
  f x | isNaN x    = Nan
  f x | isInf (-x) = Def LT
  f x | x <~ 0     = Def EQ
  f x | otherwise  = Def GT

  h x | isNaN x    = Nan
  h x | isInf x    = Def GT
  h x | x >~ 0     = Def EQ
  h x | otherwise  = Def LT

--TODO f32i64?
f32i32 :: Conn Float (Nan Int32)
f32i32 = Conn (liftNan f) (nan (0/0) g) where
  f x | abs x <~ 2**24-1 = ceiling x
      | otherwise = if x >~ 0 then 2^24 else minimal

  g i | abs' i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**24
  
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nan (0/0) f) (liftNan g) where
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


{-
-- Lattice b => Conn a b -> Conn a (Ratio b)


rationalToFloat :: Integer -> Integer -> Float

λ> rationalToFloat 0 0
NaN

λ> fromRational (0 :% 0)
NaN

λ> toRational (0/0 :: Float)
(-510423550381407695195061911147652317184) % 1

1.0000001

100000 :% 1000001
-}


-- TODO handle underflow / overflow / loss of precision
-- 
ratf32 :: Trip Rational Float
ratf32 = Trip f g h
  where h (0 :% 0) = 0/0 
        h x = Prelude.fromRational x --F.fromRat' x

        g x | F.isFloatNaN x == 1 = 0 :% 0
            | otherwise = toRational x

        help x = case pcompare x 0 of
                   Just LT -> shift (-1) x
                   Just EQ -> x
                   Just GT -> shift 1 x
                   Nothing -> 0/0

        f x = let y = h x in if g y /= x then help y else y




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
