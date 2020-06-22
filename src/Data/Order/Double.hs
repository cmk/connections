{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
-- | This module should be imported qualified.
module Data.Order.Double (
    min
  , max
  , open
  , openl
  , openr
  , covers
  , ulp
  , shift
  , within
  , lower
  , upper
  , minimal
  , maximal
  , epsilon
) where

import safe Data.Bool
import safe Data.Lattice
import safe Data.Int
import safe Data.Order
import safe Data.Order.Syntax hiding (min, max)
import safe Data.Order.Interval
import safe Data.Word
import safe Data.List (unfoldr)
import safe Data.Universe.Class
import safe GHC.Float as F
import safe Prelude hiding (Eq(..), Ord(..), Bounded, until)
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

-- | A /NaN/-handling min function.
--
-- > min x NaN = x
-- > min NaN y = y
--
min :: Double -> Double -> Double
min x y = case (isNaN x, isNaN y) of
  (False, False) -> if x <= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | A /NaN/-handling max function.
--
-- > max x NaN = x
-- > max NaN y = y
--
max :: Double -> Double -> Double
max x y = case (isNaN x, isNaN y) of
  (False, False) -> if x >= y then x else y
  (False, True) -> x
  (True, False) -> y
  (True, True)  -> x

-- | Construnct an open interval.
--
-- >>> contains 1 $ open 1 2
-- False
-- >>> contains 2 $ open 1 2
-- False
--
open :: Double -> Double -> Interval Double
open x y = shift 1 x ... shift (-1) y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ openl 1 2
-- False
-- >>> contains 2 $ openl 1 2
-- True
--
openl :: Double -> Double -> Interval Double
openl x y = shift 1 x ... y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ openr 1 2
-- True
-- >>> contains 2 $ openr 1 2
-- False
--
openr :: Double -> Double -> Interval Double
openr x y = x ... shift (-1) y

-- | Covering relation on the /N5/ lattice of doubles.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
-- >>> covers 1 (shift 1 1)
-- True
-- >>> covers 1 (shift 2 1)
-- False
--
covers :: Double -> Double -> Bool
covers x y = x ~~ shift (-1) y

-- | Generate a list of the contents on an interval.
--
-- Returns the list of values in the interval defined by a bounding pair.
--
-- Lawful variant of 'enumFromTo'.
--
indexFromTo :: Interval Double -> [Double]
indexFromTo i = case endpts i of
  Nothing -> []
  Just (x, y) -> flip unfoldr x $ \i -> if i ~~ y then Nothing else Just (i, shift 1 i)

-- | Compute the signed distance between two doubles in units of least precision.
--
-- >>> ulp 1.0 (shift 1 1.0)
-- Just (LT,1)
-- >>> ulp (0.0/0.0) 1.0
-- Nothing
--
ulp :: Double -> Double -> Maybe (Ordering, Word64)
ulp x y = fmap f $ pcompare x y
  where  x' = doubleInt64 x
         y' = doubleInt64 y
         f LT = (LT, fromIntegral . abs $ y' - x')
         f EQ = (EQ, 0)
         f GT = (GT, fromIntegral . abs $ x' - y')

-- | Shift by /n/ units of least precision.
--
-- >>> shift 1 0
-- 1.0e-45
-- >>> shift 1 $ 0/0
-- NaN
-- >>> shift (-1) $ 0/0
-- NaN
-- >>> shift 1 $ 1/0
-- Infinity
--
shift :: Int64 -> Double -> Double
shift n x | x ~~ 0/0 = x
          | otherwise = int64Double . clamp64 . (+ n) . doubleInt64 $ x

-- | Compare two double-precision floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word64 -> Double -> Double -> Bool
within tol x y = maybe False ((<= tol) . snd) $ ulp x y

-- |
--
-- @'lower64' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower :: Preorder a => Double -> (Double -> a) -> a -> Double
lower z f x = until (\y -> f y <~ x) (>~) (shift $ -1) z

-- |
--
-- @'upper64' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
upper :: Preorder a => Double -> (Double -> a) -> a -> Double
upper z g y = until (\x -> g x >~ y) (<~) (shift 1) z

-- | Minimal positive value.
--
-- >>> minimal
-- 5.0e-324
-- >>> shift (-1) minimal
-- 0
--
minimal :: Double
minimal = shift 1 0.0

-- | Maximum finite value.
--
-- >>> maximal
-- 1.7976931348623157e308
-- >>> shift 1 maximal
-- Infinity
-- >>> shift (-1) $ negate maximal
-- -Infinity
-- 
maximal :: Double
maximal = shift (-1) top 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon = shift 1 1 - 1
--
-- >>> epsilon
-- 2.220446049250313e-16
--
epsilon :: Double
epsilon = shift 1 1.0 - 1.0

--------------------------------------------------------------------------------
-- Orphans
---------------------------------------------------------------------

instance Universe Double where
  universe = 0/0 : indexFromTo (bottom ... top)

instance Finite Double

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-
f32c32 :: Conn Float CFloat
f32c32 = Conn CFloat $ \(CFloat f) -> f

f64c64 :: Conn Double CDouble
f64c64 = Conn CDouble $ \(CDouble f) -> f

f32u32 :: Conn Float Ulp32
f32u32 = Conn (Ulpf . floatInt32) (int32Float . unUlp32)

u32f32 :: Conn Ulpf Float
u32f32 = Conn (int32Float . unUlp32) (Ulpf . floatInt32)

-- correct but maybe replace w/ Graded / Yoneda / Indexed etc
u32w64 :: Conn Ulpf (Maybe Word64)
u32w64 = Conn f g where
  conn = i32wf >>> w32w64

  of32set  = 2139095041 :: Word64
  of32set' = 2139095041 :: Int32

  f x@(Ulpf y) | ulp32Maybe x = Maybe
               | neg y = Just $ fromIntegral (y + of32set')
               | otherwise = Just $ (fromIntegral y) + of32set
               where fromIntegral = connl conn

  g x = case x of
          Maybe -> Ulpf of32set'
          Just y | y < of32set -> Ulpf $ (fromIntegral y) P.- of32set'
                | otherwise  -> Ulpf $ fromIntegral ((min 4278190081 y) P.- of32set)
               where fromIntegral = connr conn

--order of magnitude
f32w08 :: Trip Float (Maybe Word8)
f32w08 = Trip (nanf f) (nan (0/0) g) (nanf h) where
  h x = if x > 0 then 0 else connr w08wf $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)

abs' :: (Eq a, Bounded a, Num a) => a -> a
abs' x = if x ~~ bottom then abs (x+1) else abs x

nanf :: (Eq a, Lattice a) => Floating a => (a -> b) -> a -> Maybe b
nanf f x | x ~~ 0/0 = Nothing
         | otherwise = Just (f x)

nan :: Fractional b => (a -> b) -> Maybe a -> b
nan = maybe (0/0)

extf f x | x ~~ 0/0 = Bottom -- ?
         | otherwise = Extended (f x)
-}



-- Non-monotonic function 
signed64 :: Word64 -> Int64
signed64 x | x < 0x8000000000000000 = fromIntegral x
           | otherwise      = fromIntegral (top P.- (x P.- 0x8000000000000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned64 :: Int64 -> Word64
unsigned64 x | x >~ 0  = fromIntegral x
             | otherwise = 0x8000000000000000 + (top P.- (fromIntegral x))

-- Clamp between the int representations of -1/0 and 1/0 
clamp64 :: Int64 -> Int64
clamp64 = P.max (-9218868437227405313) . P.min 9218868437227405312 

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

