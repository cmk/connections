{-# LANGUAGE CPP, ForeignFunctionInterface #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Re-exports from /cmath/.
--
module Data.Float (
  -- * Float
    Float
  , eqf
  , minSubf
  , minNormf
  , maxOddf
  , maxNormf
  , epsilonf
  -- * Double
  , Double
  , eq
  , minSub
  , minNorm
  , maxOdd
  , maxNorm
  , epsilon
  , cos
  , sin
  , tan
  , acos
  , asin
  , atan
  , atan2
  , cosh
  , sinh
  , tanh
  , acosh
  , asinh
  , atanh
  , exp
  , frexp
  , ldexp
  , log
  , log10
  , modf
  , pow
  , sqrt
  , floor
  , ceiling
  , round
  , truncate
  , fabs
  , fmod
  , erf 
  , erfc
  , hypot
  , j0
  , j1 
  , y0 
  , y1
  , yn 
  , lgamma
  , cbrt
  , logb
  , nextafter
  , remainder
  , scalb
  , significand
  , copysign
  , ilogb
  , rint
) where

import Data.Function (on)
import Data.Int
import Data.Prd
import Data.Prd.Nan
import Data.Word
import Data.Connection.Conn
import Data.Connection.Float
import Foreign hiding (shift)
import Foreign.C
import GHC.Float as F hiding (Fractional(..), Floating(..), RealFloat(..), RealFrac(..))
import Prelude hiding (Ord(..), Enum(..), Fractional(..), Floating(..), RealFloat(..), RealFrac(..))
import System.IO.Unsafe (unsafePerformIO)
import qualified Prelude as P


{-# LINE 28 "Foreign/C/Math/Double.hsc" #-}


-- | Compute the cosine of x, measured in radians.
--
cos :: Double -> Double
cos = mapr f64c64 c_cos
{-# INLINE cos #-}

foreign import ccall unsafe "math.h cos" c_cos      :: CDouble -> CDouble

-- | Compute the sine of x, measured in radians.
--
sin :: Double -> Double
sin = mapr f64c64 c_sin
{-# INLINE sin #-}

foreign import ccall unsafe "math.h sin" c_sin      :: CDouble -> CDouble

-- | Compute the tangent of x, measured in radians.
--
tan :: Double -> Double
tan = mapr f64c64 c_tan
{-# INLINE tan #-}

foreign import ccall unsafe "math.h tan" c_tan      :: CDouble -> CDouble

-- | Compute the principal value of the arc cosine of x in the range [0, pi].
--
acos :: Double -> Double
acos = mapr f64c64 c_acos
{-# INLINE acos #-}

foreign import ccall unsafe "math.h acos" c_acos :: CDouble -> CDouble

-- | Compute the principal value of the arc sine of x in the range [-pi/2, +pi/2].
--
asin :: Double -> Double
asin = mapr f64c64 c_asin
{-# INLINE asin #-}

foreign import ccall unsafe "math.h asin" c_asin     :: CDouble -> CDouble

-- | Compute the principal value of the arc tangent of the argument in the range [-pi/2, +pi/2].
--
atan :: Double -> Double
atan = mapr f64c64 c_atan
{-# INLINE atan #-}

foreign import ccall unsafe "math.h atan" c_atan     :: CDouble -> CDouble

-- | Compute the principal value of the arc tangent of y/x.
--
-- Uses the signs of both arguments to determine the quadrant of the return value.
--
atan2 :: Double -> Double -> Double
atan2 = map2r f64c64 c_atan2
{-# INLINE atan2 #-}

foreign import ccall unsafe "math.h atan2" c_atan2    :: CDouble -> CDouble -> CDouble

-- | The cosh function computes the hyperbolic cosine of x.
--
cosh :: Double -> Double
cosh = mapr f64c64 c_cosh
{-# INLINE cosh #-}

foreign import ccall unsafe "math.h cosh" c_cosh     :: CDouble -> CDouble

-- | Compute the hyperbolic sine of x.
--
sinh :: Double -> Double
sinh = mapr f64c64 c_sinh
{-# INLINE sinh #-}

foreign import ccall unsafe "math.h sinh" c_sinh     :: CDouble -> CDouble

-- | Compute the hyperbolic tangent of x.
--
tanh :: Double -> Double
tanh = mapr f64c64 c_tanh
{-# INLINE tanh #-}

foreign import ccall unsafe "math.h tanh" c_tanh     :: CDouble -> CDouble

------------------------------------------------------------------------

-- | Compute the exponential of x.
--
exp :: Double -> Double
exp = mapr f64c64 c_exp
{-# INLINE exp  #-}

foreign import ccall unsafe "math.h exp" c_exp      :: CDouble -> CDouble

-- | Convert a floating-point number to fractional and integral components
--
frexp :: Double -> (Double,Int)
frexp x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_frexp (realToFrac x) p
        i <- peek p
        return (realToFrac d, fromIntegral i)

foreign import ccall unsafe "math.h frexp" c_frexp    :: CDouble -> Ptr CInt -> IO Double

-- | Multiply x by an integral power of 2.
--
ldexp :: Double -> Int -> Double
ldexp x i = c_ldexp (connl f64c64 x) (fromIntegral i)
{-# INLINE ldexp #-}

foreign import ccall unsafe "math.h ldexp" c_ldexp    :: CDouble -> CInt -> Double

-- | Compute the natural logarithm of x.
--
log :: Double -> Double
log = mapr f64c64 c_log
{-# INLINE log  #-}

foreign import ccall unsafe "math.h log" c_log      :: CDouble -> CDouble

-- | Compute the base 10 logarithm of x.
--
log10 :: Double -> Double
log10 = mapr f64c64 c_log10
{-# INLINE log10 #-}

foreign import ccall unsafe "math.h log10" c_log10    :: CDouble -> CDouble

-- | Separate x into integral and fractional parts.
--
-- Each part has the same sign as the argument.
--
modf :: Double -> (Double,Double)
modf x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_modf (realToFrac x) p
        i <- peek p
        return (realToFrac d, realToFrac i)

foreign import ccall unsafe "math.h modf" c_modf     :: CDouble -> Ptr CDouble -> IO CDouble

-- | Compute the value of x raised to the exponent y.
--
pow :: Double -> Double -> Double
pow = map2r f64c64 c_pow
{-# INLINE pow #-}

foreign import ccall unsafe "math.h pow" c_pow      :: CDouble -> CDouble -> CDouble

-- | Compute the non-negative square root of x.
--
sqrt :: Double -> Double
sqrt = mapr f64c64 c_sqrt
{-# INLINE sqrt #-}

foreign import ccall unsafe "math.h sqrt" c_sqrt     :: CDouble -> CDouble

-- | Return the nearest value to x.
--
-- If x lies halfway between two values, then return the value with the
-- larger absolute value (i.e. round away from zero).
-- 
round :: Double -> Double
round = mapr f64c64 c_round
{-# INLINE round #-}

foreign import ccall unsafe "math.h round" c_round    :: CDouble -> CDouble

-- | Compute the largest integral value less than or equal to x.
--
floor :: Double -> Double
floor = mapr f64c64 c_floor
{-# INLINE floor #-}

foreign import ccall unsafe "math.h floor" c_floor    :: CDouble -> CDouble

-- | Compute the smallest integral value greater than or equal to x.
--
ceiling :: Double -> Double
ceiling = mapr f64c64 c_ceil
{-# INLINE ceiling #-}

foreign import ccall unsafe "math.h ceil" c_ceil     :: CDouble -> CDouble

-- | Truncate x towards zero.
--
truncate :: Double -> Double
truncate = mapr f64c64 c_trunc
{-# INLINE truncate #-}

foreign import ccall unsafe "math.h trunc" c_trunc    :: CDouble -> CDouble

-- | Compute the absolute value of x.
--
fabs :: Double -> Double
fabs = mapr f64c64 c_fabs
{-# INLINE fabs #-}

foreign import ccall unsafe "math.h fabs" c_fabs     :: CDouble -> CDouble

-- | Compute the floating-point remainder of x \/ y.
--
fmod :: Double -> Double -> Double
fmod = map2r f64c64 c_fmod
{-# INLINE fmod #-}

foreign import ccall unsafe "math.h fmod" c_fmod     :: CDouble -> CDouble -> CDouble

-- | Compute the error function of x.
--
-- > erf x = 2/sqrt(pi)*i
--
-- where /i/ is the integral from /0/ to /x/ of /exp(-t*t) dt/.
--
erf :: Double -> Double
erf = mapr f64c64 c_erf
{-# INLINE erf #-}

foreign import ccall unsafe "math.h erf" c_erf      :: CDouble -> CDouble

-- | Compute the complementary error function of x.
--
-- > erfc x = 1 - erf x
--
erfc :: Double -> Double
erfc = mapr f64c64 c_erfc
{-# INLINE erfc #-}

foreign import ccall unsafe "math.h erfc" c_erfc     :: CDouble -> CDouble

-- | Compute the gamma function of x.
--
gamma :: Double -> Double
gamma = mapr f64c64 c_gamma
{-# INLINE gamma #-}

foreign import ccall unsafe "math.h gamma" c_gamma    :: CDouble -> CDouble

-- | Compute /sqrt(x*x+y*y)/.
-- 
-- > hypot (1/0) x = hypot x (1/0) = 1/0
--
hypot :: Double -> Double -> Double
hypot = map2r f64c64 c_hypot
{-# INLINE hypot #-}

foreign import ccall unsafe "math.h hypot" c_hypot    :: CDouble -> CDouble -> CDouble

-- | Bessel function of the second kind of order 0,
--
j0 :: Double -> Double
j0 = mapr f64c64 c_j0
{-# INLINE j0 #-}

foreign import ccall unsafe "math.h j0" c_j0    :: CDouble -> CDouble

-- | Bessel function of the second kind of order 1,
--
j1 :: Double -> Double
j1 = mapr f64c64 c_j1
{-# INLINE j1 #-}

foreign import ccall unsafe "math.h j1" c_j1    :: CDouble -> CDouble

-- | Linearly independent Bessel function of the second kind of order 0,
--
y0 :: Double -> Double
y0 = mapr f64c64 c_y0
{-# INLINE y0 #-}

foreign import ccall unsafe "math.h y0" c_y0    :: CDouble -> CDouble

-- | Linearly independent Bessel function of the second kind of order 1,
--
y1 :: Double -> Double
y1 = mapr f64c64 c_y1
{-# INLINE y1 #-}

foreign import ccall unsafe "math.h y1" c_y1    :: CDouble -> CDouble

-- | Bessel function of the second kind.
--
yn :: Int -> Double -> Double
yn i = mapr f64c64 $ c_yn (fromIntegral i)
{-# INLINE yn #-}

foreign import ccall unsafe "math.h yn" c_yn    :: CInt -> CDouble -> CDouble

-- | Compute /ln|gamma x|/.
--
lgamma :: Double -> Double
lgamma = mapr f64c64 c_lgamma 
{-# INLINE lgamma #-}

foreign import ccall unsafe "math.h lgamma" c_lgamma    :: CDouble -> CDouble

-- | Compute the inverse hyperbolic cosine of x.
--
acosh :: Double -> Double
acosh = mapr f64c64 c_acosh
{-# INLINE acosh #-}

foreign import ccall unsafe "math.h acosh" c_acosh    :: CDouble -> CDouble

-- | Compute the inverse hyperbolic sine of x.
--
asinh :: Double -> Double
asinh = mapr f64c64 c_asinh
{-# INLINE asinh #-}

foreign import ccall unsafe "math.h asinh" c_asinh    :: CDouble -> CDouble

-- | Compute the inverse hyperbolic tangent of x.
--
atanh :: Double -> Double
atanh = mapr f64c64 c_atanh
{-# INLINE atanh #-}

foreign import ccall unsafe "math.h atanh" c_atanh    :: CDouble -> CDouble

-- | Compute the cube root of x.
--
cbrt :: Double -> Double
cbrt = mapr f64c64 c_cbrt
{-# INLINE cbrt #-}

foreign import ccall unsafe "math.h cbrt" c_cbrt    :: CDouble -> CDouble

-- | Return the floor of the argument's exponent.
-- 
-- > logb (1/0) = 1/0
-- > logb 0 = -1/0
--
logb :: Double -> Double
logb = mapr f64c64 c_logb
{-# INLINE logb #-}

foreign import ccall unsafe "math.h logb" c_logb    :: CDouble -> CDouble

-- | Return the next machine representable number from x in the direction of y.
--
nextafter :: Double -> Double -> Double
nextafter = map2r f64c64 c_nextafter
{-# INLINE nextafter #-}

foreign import ccall unsafe "math.h nextafter" c_nextafter    :: CDouble -> CDouble -> CDouble

-- | Return the remainder of x with after division by y.
--
-- > remainder x y = x - n*y
--
-- where n is the integer nearest the exact value of @x/y@.
--
-- /Caution/: /remainder x 0/ will return -Infinity.
--
remainder :: Double -> Double -> Double
remainder = map2r f64c64 c_remainder
{-# INLINE remainder #-}

foreign import ccall unsafe "math.h remainder" c_remainder    :: CDouble -> CDouble -> CDouble

-- | Prefix variant of /**/.
-- 
-- > scalb x n = x * 2**n
--
scalb :: Double -> Double -> Double
scalb = map2r f64c64 c_scalb
{-# INLINE scalb #-}

foreign import ccall unsafe "math.h scalb" c_scalb    :: CDouble -> CDouble -> CDouble

-- | Return the significand of the argument.
--
-- > x = significand x * 2**n
--
-- /Caution/: 'significand' is not defined when x is 0, +-Infinity, or NaN.
--
significand :: Double -> Double
significand = mapr f64c64 c_significand
{-# INLINE significand #-}

foreign import ccall unsafe "math.h significand" c_significand    :: CDouble -> CDouble

-- | Return x with its sign changed to that of y.
--
copysign :: Double -> Double -> Double
copysign = map2r f64c64 c_copysign
{-# INLINE copysign #-}

foreign import ccall unsafe "math.h copysign" c_copysign    :: CDouble -> CDouble -> CDouble

-- | Return the base 2 exponent of x.
-- 
-- > ilogb (1/0) = maximal
-- > ilogb 0 = minimal
--
ilogb :: Double -> Int
ilogb x = fromIntegral $ c_ilogb (connl f64c64 x)
{-# INLINE ilogb #-}

foreign import ccall unsafe "math.h ilogb" c_ilogb    :: CDouble -> CInt

-- | Compute the integral value nearest to x according to the prevailing rounding mode.
--
rint :: Double -> Double
rint = mapr f64c64 c_rint
{-# INLINE rint #-}

foreign import ccall unsafe "math.h rint" c_rint    :: CDouble -> CDouble


{-
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
    x <= y | ulp32Nan x && ulp32Nan y = True
           | ulp32Nan x || ulp32Nan y = False
           | otherwise                = on (<=) unUlp32 x y

instance Minimal Ulp32 where
    minimal = Ulp32 $ -2139095041

instance Maximal Ulp32 where
    maximal = Ulp32 $ 2139095040

-- internal


signBit :: Double -> Bool
signBit x = if x =~ 0/0 then False else msbMask x /= 0

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
signBitf x = if x =~ 0/0 then False else msbMaskf x /= 0

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




