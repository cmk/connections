{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Float (
    Float
  , module Data.Float
  , module F
) where

import Prelude hiding (Num(..), Fractional(..), Floating(..),  (^^), (^), RealFloat(..), Real(..), Enum(..))

import Control.Category ((>>>))
import Foreign.C
import Data.Word
import Data.Prd.Nan hiding (isNan)
import Data.Int
import Data.Prd
import Data.Semifield
import Data.Semiring
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Data.Function (on)
import Data.Connection 

import Data.Bits ((.&.))


import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Data.Ratio

import qualified Prelude as P
import qualified Control.Category as C
import qualified Data.Bits as B
import GHC.Float as F
import qualified GHC.Float.RealFracMethods as R


----------------------------------------------------------------
-- Float utils
----------------------------------------------------------------


-- | Bitwise equality.
eqf :: Float -> Float -> Bool
eqf = (==) `on` floatWord32

signBitf :: Float -> Bool
signBitf x = if x =~ anan then False else msbMask x /= 0

evenBitf :: Float -> Bool
evenBitf x = lsbMask x == 0

-- | maximal (positive) finite value.
maxNormf :: Float
maxNormf = shiftf (-1) maximal 

-- | minimal (positive) normalized value.
minNormf :: Float
minNormf = word32Float 0x00800000

-- | maximal representable odd integer. 
--
-- @ maxOddf = 2**24 - 1@
--
maxOddf :: Float
maxOddf = 16777215

-- | minimal (positive) value.
minSubf :: Float
minSubf = shiftf 1 0

-- | difference between 1 and the smallest representable value greater than 1.
epsilonf :: Float
epsilonf = shiftf 1 1 - 1

splitf :: Float -> Either Float Float
splitf x = case signBitf x of
  True -> Left x
  _    -> Right x


-- | Shift by /Int32/ units of least precision.

-- TODO replace w/ Yoneda / Index / Graded
shiftf :: Int32 -> Float -> Float
shiftf n = int32Float . (+ n) . floatInt32

-- | Compare two 'Float' values for approximate equality, using
-- Dawson's method.
--
-- required accuracy is specified in ULPs (units of least
-- precision).  If the two numbers differ by the given number of ULPs
-- or less, this function returns @True@.
withinf :: Word32 -> Float -> Float -> Bool
withinf tol a b = ulpDistance a b <~ tol


ulps :: Float -> Float -> (Bool, Word32)
ulps x y = o
  where  x' = floatInt32 x
         y' = floatInt32 y
         o  | x' >~ y' = (False, fromIntegral . abs $ x' - y')
            | otherwise = (True, fromIntegral . abs $ y' - x')

ulpDistance :: Float -> Float -> Word32
ulpDistance x y = snd $ ulps x y

ulpDelta :: Float -> Float -> Int
ulpDelta x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d

ulpDelta' :: Float -> Float -> Int32
ulpDelta' x y = if lesser then d' else (-1) * d'
  where (lesser, d) = ulps x y
        d' = fromIntegral d


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
    x <~ y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<~) unUlp32 x y

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
    Join (Ulp32 x) <> Join (Ulp32 y) = Join . Ulp32 $ max x y

instance Semigroup (Meet Ulp32) where
    Meet (Ulp32 x) <> Meet (Ulp32 y) = Meet . Ulp32 $ min x y

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
                | negative y = Def $ fromIntegral (y + offset')
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


lsbMask :: Float -> Word32
lsbMask x = 0x00000001 .&. floatWord32 x

msbMask :: Float -> Word32
msbMask x = 0x80000000 .&. floatWord32 x

-- floatWord32 maximal == exponent maximal
expMask :: Float -> Word32
expMask x = 0x7f800000 .&. floatWord32 x

-- chk f = f >= 0 ==> f == word32Float $ exponent f + significand f
sigMask :: Float -> Word32
sigMask x = 0x007FFFFF .&. floatWord32 x



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

-- TODO force to positive representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32

