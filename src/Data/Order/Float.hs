{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
-- | This module should be imported qualified.
module Data.Order.Float (
    min
  , max
  , open
  , openl
  , openr
  , covers
  , indexFromTo
  , ulp
  , shift
  , within
  , lower32
  , upper32
  , minimal
  , maximal
  , epsilon
) where

import safe Data.Bool
import safe Data.Lattice
import safe Data.Int
import safe Data.Order
import safe Data.Order.Interval
import safe Data.Order.Syntax hiding (min, max)
import safe Data.Word
import safe Data.List (unfoldr)
import safe Data.Universe.Class
import safe GHC.Float (float2Double,double2Float)
import safe GHC.Float as F
import safe Prelude as P hiding (Eq(..), Ord(..), Bounded, until)
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | A /NaN/-handling min function.
--
-- > min x NaN = x
-- > min NaN y = y
--
min :: Float -> Float -> Float
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
max :: Float -> Float -> Float
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
open :: Float -> Float -> Interval Float
open x y = shift 1 x ... shift (-1) y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ openl 1 2
-- False
-- >>> contains 2 $ openl 1 2
-- True
--
openl :: Float -> Float -> Interval Float
openl x y = shift 1 x ... y

-- | Construnct a half-open interval.
--
-- >>> contains 1 $ openr 1 2
-- True
-- >>> contains 2 $ openr 1 2
-- False
--
openr :: Float -> Float -> Interval Float
openr x y = x ... shift (-1) y

-- | Covering relation on the /N5/ lattice of floats.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
-- >>> covers 1 (shift 1 1)
-- True
-- >>> covers 1 (shift 2 1)
-- False
--
covers :: Float -> Float -> Bool
covers x y = x ~~ shift (-1) y

-- | Generate a list of the contents on an interval.
--
-- Returns the list of values in the interval defined by a bounding pair.
--
-- Lawful variant of 'enumFromTo'.
--
indexFromTo :: Interval Float -> [Float]
indexFromTo i = case endpts i of
  Nothing -> []
  Just (x, y) -> flip unfoldr x $ \i -> if i ~~ y then Nothing else Just (i, shift 1 i)

-- | Compute the signed distance between two floats in units of least precision.
--
-- >>> ulp 1.0 (shift 1 1.0)
-- Just (LT,1)
-- >>> ulp (0.0/0.0) 1.0
-- Nothing
--
ulp :: Float -> Float -> Maybe (Ordering, Word32)
ulp x y = fmap f $ pcompare x y
  where  x' = floatInt32 x
         y' = floatInt32 y
         f LT = (LT, fromIntegral . abs $ y' - x')
         f EQ = (EQ, 0)
         f GT = (GT, fromIntegral . abs $ x' - y')

-- | Shift a float by /n/ units of least precision.
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
shift :: Int32 -> Float -> Float
shift n x | x ~~ 0/0 = x
          | otherwise = int32Float . clamp32 . (+ n) . floatInt32 $ x

-- | Compare two floats for approximate equality.
--
-- Required accuracy is specified in units of least precision.
--
-- See also <https://randomascii.wordpress.com/2012/02/25/comparing-floating-point-numbers-2012-edition/>.
-- 
within :: Word32 -> Float -> Float -> Bool
within tol x y = maybe False ((<= tol) . snd) $ ulp x y

-- |
--
-- @'lower32' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
lower32 :: Preorder a => Float -> (Float -> a) -> a -> Float
lower32 z f x = until (\y -> f y <~ x) (>~) (shift $ -1) z

-- |
--
-- @'upper32' y@ is the greatest element /x/ in the ascending
-- chain such that @not $ g x '>~' y@.
--
upper32 :: Preorder a => Float -> (Float -> a) -> a -> Float
upper32 z g y = until (\x -> g x >~ y) (<~) (shift 1) z

-- | Minimal positive value.
--
-- >>> minimal
-- 1.0e-45
-- >>> shift (-1) minimal
-- 0
--
minimal :: Float
minimal = shift 1 0.0

-- | Maximum finite value.
--
-- >>> maximal
-- 3.4028235e38
-- >>> shift 1 maximal
-- Infinity
-- >>> shift (-1) $ negate maximal
-- -Infinity
--
maximal :: Float
maximal = shift (-1) top 

-- | Difference between 1 and the smallest representable value greater than 1.
--
-- > epsilon = shift 1 1 - 1
--
-- >>> epsilon
-- 1.1920929e-7
--
epsilon :: Float
epsilon = shift 1 1.0 - 1.0

---------------------------------------------------------------------
-- Orphans
---------------------------------------------------------------------

instance Universe Float where
  universe = 0/0 : indexFromTo (bottom ... top)

instance Finite Float

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

{-

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
signed32 :: Word32 -> Int32
signed32 x | x P.< 0x80000000 = fromIntegral x
           | otherwise      = fromIntegral (top P.- (x P.- 0x80000000))

-- Non-monotonic function converting from 2s-complement format.
unsigned32 :: Int32 -> Word32
unsigned32 x | x P.>= 0  = fromIntegral x
             | otherwise = 0x80000000 + (top P.- (fromIntegral x))

-- Clamp between the int representations of -1/0 and 1/0 
clamp32 :: Int32 -> Int32
clamp32 = P.max (-2139095041) . P.min 2139095040

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
