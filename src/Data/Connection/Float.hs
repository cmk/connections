module Data.Connection.Float (
    fltord
  -- * Float
  , TripFloat(..)
  , round32
  , trunc32
  , floor32
  , ceiling32
  , f32i08
  , f32i16
  , f32i32
  , i32f32
  -- * Double
  , TripDouble(..)
  , round64
  , trunc64
  , floor64
  , ceiling64
  , f64i08
  , f64i16
  , f64i32
  , f64i64
  , i64f64
) where

import Data.Bool
import Data.Connection
import Data.Connection.Round
import Data.Float hiding (round)
import Data.Int
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Top
import Prelude as P hiding (Ord(..), Bounded)


fltord :: Prd a => Floating a => Trip a (Nan Ordering)
fltord = Trip f g h where
  g (Def GT) = (1/0) 
  g (Def LT) = (-1/0) 
  g (Def EQ) = 0
  g Nan = 0/0 
  
  f x | x =~ 0/0  = Nan
      | x =~ (-1/0)  = Def LT
      | x <= 0  = Def EQ
      | otherwise  = Def GT

  h x | x =~ 0/0  = Nan
      | x =~ (1/0)  = Def GT
      | x >= 0  = Def EQ
      | otherwise  = Def LT

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

class Prd a => TripFloat a where
  f32typ :: Trip Float (Extended a)

instance TripFloat Int8 where f32typ = f32i08

instance TripFloat Int16 where f32typ = f32i16

-- | 
--
-- >>> round @Float @Int8 $ 0/0
-- 0
-- >>> round @Float @Int8 $ 1/0
-- 0
-- >>> round @Float @Int8 129
-- -127
-- >>> round @Float @Int8 $ -129
-- 127
-- >>> round @Float @Int8 $ -130
-- 126
-- >>> round32 @Int8 $ 0/0
-- Nan
-- >>> round32 @Int8 $ 1/0
-- Def 127
-- >>> round32 @Int8 129
-- Def 127
-- >>> round32 @Int8 $ -129
-- Def (-128)
-- >>> round32 @Int8 $ -130
-- Def (-128)
-- >>> round32 5.3 :: Nan Int8
-- Def 5
-- >>> round32 (-5.3) :: Nan Int8
-- Def (-5)
-- 
round32 :: forall a. Bounded a => Num a => TripFloat a => Float -> Nan a
round32 x = maybe Nan f $ half @Float @(Extended a) f32typ x where
  f LT = floor32 x
  f GT = ceiling32 x
  f EQ = trunc32 x --TODO: round to even

trunc32 :: Bounded a => Num a => TripFloat a => Float -> Nan a
trunc32 x = maybe Nan f $ sign x where
  f LT = ceiling32 x
  f GT = floor32 x
  f EQ = Def 0

-- | A monotonic floor function.
--
floor32 :: Bounded a => TripFloat a => Float -> Nan a
floor32 = fmap (bounded id) . floorOn f32typ

-- | A monotonic ceiling function.
--
-- >>> ceiling @Float @Int8 129
-- -127
-- >>> ceiling32 @Int8 129
-- Def 127
-- >>> ceiling @Float @Int8 (0/0)
-- 0
-- >>> ceiling32 @Int8 (0/0)
-- Nan
--
ceiling32 :: Bounded a => TripFloat a => Float -> Nan a
ceiling32 = fmap (bounded id) . ceilingOn f32typ

-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = Trip (liftNan f) (nanf g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Float'.
f32i16 :: Trip Float (Extended Int16)
f32i16 = Trip (liftNan f) (nanf g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: Conn Float (Nan Int32)
f32i32 = Conn (liftNan f) (nanf g) where
  f x | abs x <= 2**24-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^24 else minimal

  g i | abs' i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Nan Int32) Float
i32f32 = Conn (nanf g) (liftNan f) where
  f x | abs x <= 2**24-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^24

  g i | abs i <= 2^24-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**24 else -1/0

---------------------------------------------------------------------
-- Double
---------------------------------------------------------------------

class Prd a => TripDouble a where
  f64typ :: Trip Double (Extended a)

instance TripDouble Int8 where f64typ = f64i08

instance TripDouble Int16 where f64typ = f64i16

instance TripDouble Int32 where f64typ = f64i32

round64 :: forall a. Bounded a => Num a => TripDouble a => Double -> Nan a
round64 x = maybe Nan f $ half @Double @(Extended a) f64typ x where
  f LT = floor64 x
  f GT = ceiling64 x
  f EQ = trunc64 x --TODO: round to even

trunc64 :: Bounded a => Num a => TripDouble a => Double -> Nan a
trunc64 x = maybe Nan f $ sign x where
  f LT = ceiling64 x
  f GT = floor64 x
  f EQ = Def 0

-- | A monotonic floor function.
--
floor64 :: Bounded a => TripDouble a => Double -> Nan a
floor64 = fmap (bounded id) . floorOn f64typ

-- | A monotonic ceiling function.
--
ceiling64 :: Bounded a => TripDouble a => Double -> Nan a
ceiling64 = fmap (bounded id) . ceilingOn f64typ

-- | All 'Int8' values are exactly representable in a 'Double'.
f64i08 :: Trip Double (Extended Int8)
f64i08 = Trip (liftNan f) (nanf g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 127 

  imin = -128

-- | All 'Int16' values are exactly representable in a 'Double'.
f64i16 :: Trip Double (Extended Int16)
f64i16 = Trip (liftNan f) (nanf g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 32767 

  imin = -32768

-- | All 'Int32' values are exactly representable in a 'Double'.
f64i32 :: Trip Double (Extended Int32)
f64i32 = Trip (liftNan f) (nanf g) (liftNan h) where
  f x | x > imax = Just Top
      | x =~ (-1/0) = Nothing
      | x < imin = fin minimal
      | otherwise = fin $ P.ceiling x

  g = bound (-1/0) (1/0) P.fromIntegral

  h x | x =~ (1/0) = Just Top
      | x > imax = fin maximal
      | x < imin = Nothing
      | otherwise = fin $ P.floor x

  imax = 2147483647 

  imin = -2147483648

-- | Exact embedding up to the largest representable 'Int64'.
f64i64 :: Conn Double (Nan Int64)
f64i64 = Conn (liftNan f) (nanf g) where
  f x | abs x <= 2**53-1 = P.ceiling x
      | otherwise = if x >= 0 then 2^53 else minimal

  g i | abs' i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 1/0 else -2**53
  
-- | Exact embedding up to the largest representable 'Int64'.
i64f64 :: Conn (Nan Int64) Double
i64f64 = Conn (nanf g) (liftNan f) where
  f x | abs x <= 2**53-1 = P.floor x
      | otherwise = if x >= 0 then maximal else -2^53

  g i | abs i <= 2^53-1 = fromIntegral i
      | otherwise = if i >= 0 then 2**53 else -1/0

abs' :: Ord a => Minimal a => Num a => a -> a
abs' x = if x =~ minimal then abs (x+1) else abs x

{- 
f32w08 :: Trip Float (Nan Word8)
f32w08 = Trip (liftNan f) (nan (0/0) g) (liftNan h) where
  h x = if x > 0 then 0 else connr w08w32 $ B.shift (floatWord32 x) (-23)
  g = word32Float . flip B.shift 23 . connl w08w32
  f x = 1 + min 254 (h x)



floatDouble :: Float -> Double
floatDouble = int64Double . (* 2^ 31) . fromIntegral . floatInt32

foo :: Float -> Double
foo x = int64Double $ e' + s' where
  s' = fromIntegral s * 2^32
  e' = fromIntegral e * 2^35
  (e,s) = signed32 . expMaskf &&& signed32 . sigMaskf $ x

bar x = (e,s) where (e,s) = signed32 . expMaskf &&& signed32 . sigMaskf $ x

f64f32 :: Trip Double Float
f64f32 = Trip f g h where
  f = (fromIntegral . round) :: Double -> Float
  g = floatDouble
  h :: Double -> Float
  h x | abs x <= 1.0e-45 = case sign x of
                             Nothing -> 0/0
                             Just LT -> -minSubf
                             Just EQ -> 0
                             Just GT -> minSubf
      | otherwise = (fromIntegral . round) x
-}
