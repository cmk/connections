{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Float (
    module Data.Float
  , module F
) where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Connection 
import Data.Function (on)
import Data.Int
import Data.Prd
import Data.Prd.Nan hiding (isNan)
import Data.Ratio
import Data.Semifield
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Data.Semiring
import Data.Word
import Foreign.C
import GHC.Float as F
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Prelude hiding (Ord(..), Num(..), Fractional(..), Floating(..),  (^^), (^), RealFloat(..), Real(..), Enum(..))
import qualified Control.Category as C
import qualified Data.Bits as B
import qualified GHC.Float.RealFracMethods as R
import qualified Prelude as P

-- | Determine bitwise equality.
--
eq :: Double -> Double -> Bool
eq = (==) `on` doubleWord64

eqf :: Float -> Float -> Bool
eqf = (==) `on` floatWord32

-- | Maximum finite value.
--
-- >>> shift 1 maxNorm
-- Infinity
-- 
maxNorm :: Double
maxNorm = shift (-1) maximal 

maxNormf :: Float
maxNormf = shiftf (-1) maximal 

-- | Minimum normalized value.
--
-- >>> shift (-1) minNorm
-- 0
-- 
minNorm :: Double
minNorm = word64Double 0x0080000000000000

minNormf :: Float
minNormf = word32Float 0x00800000

-- | Maximum representable odd integer. 
--
-- @ maxOdd = 2**53 - 1@
--
maxOdd :: Double
maxOdd = 9.007199254740991e15

-- | Maximum representable odd integer. 
--
-- @ maxOddf = 2**24 - 1@
--
maxOddf :: Float
maxOddf = 1.6777215e7

-- | Minimum (pos) value.
--
-- >>> shift (-1) minSub
-- 0.0
-- 
minSub :: Double
minSub = shift 1 0

minSubf :: Float
minSubf = shiftf 1 0

-- | Difference between 1 and the smallest representable value greater than 1.
epsilon :: Double
epsilon = shift 1 1 - 1

epsilonf :: Float
epsilonf = shiftf 1 1 - 1

-- | Split a 'Double' symmetrically along the sign bit.
--
-- >>> split 0
-- Right 0.0
-- >>> split (shift (-1) 0)
-- Left (-0.0)
-- 
split :: Double -> Either Double Double
split x = case signBit x of
  True -> Left x
  _    -> Right x

splitf :: Float -> Either Float Float
splitf x = case signBitf x of
  True -> Left x
  _    -> Right x


-- TODO replace w/ Yoneda / Index / Graded
-- | Shift by /Int64/ units of least precision.
--
shift :: Int64 -> Double -> Double
shift n = int64Double . (+ n) . doubleInt64

shiftf :: Int32 -> Float -> Float
shiftf n = int32Float . (+ n) . floatInt32

-- | Compute signed distance in units of least precision.
--
-- @ 'ulps' x ('shift' ('abs' n) x) '==' ('True', 'abs' n) @
--
ulps :: Double -> Double -> (Bool, Word64)
ulps x y = o
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         o  | x' >= y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

ulpsf :: Float -> Float -> (Bool, Word32)
ulpsf x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' >= y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

-- | Compute distance in units of least precision.
--
-- @ 'ulps'' x ('shift' n x) '==' 'abs' n @
--
ulps' :: Double -> Double -> Word64
ulps' x y = snd $ ulps x y

ulpsf' :: Float -> Float -> Word32
ulpsf' x y = snd $ ulpsf x y

-- | Compare two values for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word64 -> Double -> Double -> Bool
within tol a b = ulps' a b <= tol

withinf :: Word32 -> Float -> Float -> Bool
withinf tol a b = ulpsf' a b <= tol



{-
ulpDelta :: Float -> Float -> Int
ulpDelta x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d

ulpDelta' :: Float -> Float -> Int32
ulpDelta' x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d
-}

----------------------------------------------------------------
-- Ulp32
----------------------------------------------------------------

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
    x <= y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<=) unUlp32 x y

instance Minimal Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Maximal Ulp32 where
    maximal = Ulp32 $ 2139095040

instance Semigroup (Additive Ulp32) where
    Additive (Ulp32 x) <> Additive (Ulp32 y) = Additive . Ulp32 $ x + y

instance Monoid (Additive Ulp32) where
    mempty = Additive $ Ulp32 0

instance Semigroup (Multiplicative Ulp32) where
    Multiplicative (Ulp32 x) <> Multiplicative (Ulp32 y) = Multiplicative . Ulp32 $ x * y

instance Monoid (Multiplicative Ulp32) where
    mempty = Multiplicative $ Ulp32 1

instance Presemiring Ulp32
instance Semiring Ulp32

instance Semigroup (Join Ulp32) where
    Join (Ulp32 x) <> Join (Ulp32 y) = Join . Ulp32 $ P.max x y

instance Semigroup (Meet Ulp32) where
    Meet (Ulp32 x) <> Meet (Ulp32 y) = Meet . Ulp32 $ P.min x y

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulp32 . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulp32 Float
u32f32 = Conn (int32Float . unUlp32) (Ulp32 . floatInt32)

-- fromIntegral (maxBound :: Ulp32) + 1 , image of aNan


--newtype Ulp a = Ulp { unUlp :: a }
-- instance 
{- correct but should replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulp32 (Nan Word64)
u32w64 = Conn f g where
  conn = i32w32 >>> w32w64

  offset  = 2139095041 :: Word64
  offset' = 2139095041 :: Int32

  f x@(Ulp32 y) | ulp32Nan x = Nan
                | neg y = Def $ fromIntegral (y + offset')
                | otherwise = Def $ (fromIntegral y) + offset
               where fromIntegral = connl conn

  g x = case x of
          Nan -> Ulp32 offset'
          Def y | y < offset -> Ulp32 $ (fromIntegral y) P.- offset'
                | otherwise  -> Ulp32 $ fromIntegral ((min 4278190081 y) P.- offset)
               where fromIntegral = connr conn
-}


-- internal

--
--TODO handle neg case, get # of nans/denormals, collect constants         

--abs' :: Eq a => Ord a => Bound a => Ring a => a -> a
--abs' x = if x == minimal then abs (x+one) else abs x

signBit :: Double -> Bool
signBit x = if x =~ anan then False else msbMask x /= 0

evenBit :: Double -> Bool
evenBit x = lsbMask x == 0

lsbMask :: Double -> Word64
lsbMask x = 0x0000000000000001 .&. doubleWord64 x

msbMask :: Double -> Word64
msbMask x = 0x8000000000000000 .&. doubleWord64 x

-- loatWord64 maximal == exponent maximal
--expMask :: Double -> Word64
--expMask x = 0x7F80000000000000 .&. doubleWord64 x

-- chk  =  >= 0 ==>  == word64Double $ exponent  + signiicand 
sigMask :: Double -> Word64
sigMask x = 0x007FFFFFFFFFFFFF .&. doubleWord64 x



signBitf :: Float -> Bool
signBitf x = if x =~ anan then False else msbMaskf x /= 0

evenBitf :: Float -> Bool
evenBitf x = lsbMaskf x == 0

lsbMaskf :: Float -> Word32
lsbMaskf x = 0x00000001 .&. floatWord32 x

msbMaskf :: Float -> Word32
msbMaskf x = 0x80000000 .&. floatWord32 x

-- floatWord32 maximal == exponent maximal
expMaskf :: Float -> Word32
expMaskf x = 0x7f800000 .&. floatWord32 x

-- chk f = f >= 0 ==> f == word32Float $ exponent f + significand f
sigMaskf :: Float -> Word32
sigMaskf x = 0x007FFFFF .&. floatWord32 x



{-
-- | first /NaN/ value. 
--naN :: Float
--naN = 0/0 -- inc pInf 

-- | Positive infinity
--
-- @nInf = 1/0@
--
pInf :: Float
pInf = word32Float 0x7f800000

-- | Negative infinity
--
-- @nInf = -1/0@
--
nInf :: Float
nInf = word32Float 0xff800000 
-}


-- Non-monotonic function 
signed64 :: Word64 -> Int64
signed64 x | x < 0x8000000000000000 = fromIntegral x
           | otherwise      = fromIntegral (maximal P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x | x >= 0  = fromIntegral x
             | otherwise = 0x8000000000000000 + (maximal P.- (fromIntegral x))

int64Double :: Int64 -> Double
int64Double = word64Double . unsigned64

doubleInt64 :: Double -> Int64
doubleInt64 = signed64 . doubleWord64 

-- Bit-for-bit conversion.
word64Double :: Word64 -> Double
word64Double = F.castWord64ToDouble

-- TODO force to pos representation?
-- Bit-for-bit conversion.
doubleWord64 :: Double -> Word64
doubleWord64 = (+0) . F.castDoubleToWord64

-- Non-monotonic function 
signed32 :: Word32 -> Int32
signed32 x | x < 0x80000000 = fromIntegral x
           | otherwise      = fromIntegral (maximal P.- (x P.- 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x >= 0  = fromIntegral x
             | otherwise = 0x80000000 + (maximal P.- (fromIntegral x))

int32Float :: Int32 -> Float
int32Float = word32Float . unsigned32

floatInt32 :: Float -> Int32
floatInt32 = signed32 . floatWord32 

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- TODO force to pos representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32

