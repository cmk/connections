{-# Language ConstraintKinds #-}
{-# Language Safe            #-}
module Data.Connection.Float (
  -- * Connections
    f32i08
  , f32i16
  --, f32i32
  --, i32f32
) where

import safe Data.Bool
import safe Data.Connection.Type
import safe Data.Lattice
import safe Data.Int
import safe Data.Order
import safe Data.Order.Extended
import safe GHC.Float as F
import safe Prelude as P hiding (Ord(..), Bounded, until)
import safe qualified Prelude as P

---------------------------------------------------------------------
-- Float
---------------------------------------------------------------------

-- | All 'Int08' values are exactly representable in a 'Float'.
f32i08 :: Trip Float (Extended Int8)
f32i08 = signedTriple 127

-- | All 'Int16' values are exactly representable in a 'Float'.
f32i16 :: Trip Float (Extended Int16)
f32i16 = signedTriple 32767


{-

-- | Exact embedding up to the largest representable 'Int32'.
f32i32 :: Conn Float (Maybe Int32)
f32i32 = Conn (nanf f) (nan g) where
  f x | abs x <~ 2**24-1 = P.ceiling x
      | otherwise = if x >~ 0 then 2^24 else bottom

  g i | abs' i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 1/0 else -2**24

-- | Exact embedding up to the largest representable 'Int32'.
i32f32 :: Conn (Maybe Int32) Float
i32f32 = Conn (nan g) (nanf f) where
  f x | abs x <~ 2**24-1 = P.floor x
      | otherwise = if x >~ 0 then top else -2^24

  g i | abs i <~ 2^24-1 = fromIntegral i
      | otherwise = if i >~ 0 then 2**24 else -1/0
-}


---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

signedTriple :: (Bounded a, Integral a) => Float -> Trip Float (Extended a)
signedTriple high = Trip f g h where

  f = liftExtended (~~ -1/0) (\x -> x ~~ 0/0 || x > high) $ \x -> if x < low then bottom else P.ceiling x

  g = extended bottom top P.fromIntegral
 
  h = liftExtended (\x -> x ~~ 0/0 || x < low) (~~ 1/0) $ \x -> if x > high then top else P.floor x

  low = -1 - high

{-

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

-- Bit-for-bit conversion.
word32Float :: Word32 -> Float
word32Float = F.castWord32ToFloat

-- TODO force to pos representation?
-- Bit-for-bit conversion.
floatWord32 :: Float -> Word32
floatWord32 = (+0) .  F.castFloatToWord32
-}

