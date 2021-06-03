{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Class (
    castL,
    castR,
    Triple,
    CastInteger,
    fromInteger,
    CastRational,
    fromRational,
    CastFloating,
    fromFloating,
    Connection (..),
) where

import safe Control.Category ((>>>))
import safe Data.Connection.Cast
import safe Data.Connection.Fixed
import safe Data.Connection.Float
import safe Data.Connection.Int
import safe Data.Connection.Ratio
import safe Data.Connection.Time
import safe Data.Connection.Word
import safe Data.Functor.Identity
import safe Data.Int
import safe Data.Order
import safe Data.Word
import safe Numeric.Natural
import safe Prelude hiding (ceiling, floor, fromInteger, fromRational, round, truncate)

-- | A constraint kind representing an <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
type Triple a b = (Connection 'L a b, Connection 'R a b)

-- | A < https://ncatlab.org/nlab/show/adjoint+string chain > of Galois connections of length 2 or 3.
class (Preorder a, Preorder b) => Connection k a b where

    cast :: Cast k a b

-- | A specialization of 'cast' to left-side connections.
castL :: Connection 'L a b => Cast 'L a b
castL = cast @ 'L

-- | A specialization of 'cast' to right-side connections.
castR :: Connection 'R a b => Cast 'R a b
castR = cast @ 'R

type CastInteger a = Connection 'L a (Maybe Integer)

-- | A replacement for the version in /base/.
--
--  Usable in conjunction with /RebindableSyntax/:
{-# INLINE fromInteger #-}
fromInteger :: CastInteger a => Integer -> a
fromInteger = upper cast . Just

type CastRational a = Triple Rational a

-- | A replacement for the version in /base/.
--
-- Usable in conjunction with /RebindableSyntax/:
{-# INLINE fromRational #-}
fromRational :: forall a. CastRational a => Rational -> a
fromRational x = case pcompare r l of
    Just GT -> ceiling castL x
    Just LT -> floor castR x
    _ -> if x >~ 0 then floor castR x else ceiling castL x
  where
    r = x - lower1 (castR @Rational @a) id x -- dist from lower bound
    l = upper1 (castL @Rational @a) id x - x -- dist from upper bound

type CastFloating a b = Connection 'L a (Extended b)

-- | Convert a rational or floating-point value.
--
--  The extra two arguments correspond to negative infinity and
--  to NaN / positive infinity.
{-# INLINE fromFloating #-}
fromFloating :: CastFloating a b => b -> b -> a -> b
fromFloating ninf inf = extended ninf inf id . ceiling cast

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Preorder a => Connection k a a where cast = identity

instance Connection k Ordering Bool where cast = bounds'
instance Connection k Word8 Bool where cast = bounds'
instance Connection k Word16 Bool where cast = bounds'
instance Connection k Word32 Bool where cast = bounds'
instance Connection k Word64 Bool where cast = bounds'
instance Connection k Word Bool where cast = bounds'
instance Connection k Int8 Bool where cast = bounds'
instance Connection k Int16 Bool where cast = bounds'
instance Connection k Int32 Bool where cast = bounds'
instance Connection k Int64 Bool where cast = bounds'
instance Connection k Int Bool where cast = bounds'
instance Connection k Rational Bool where cast = bounds (-1 :% 0) (1 :% 0)
instance Connection k Float Bool where cast = bounds (-1 / 0) (1 / 0)
instance Connection k Double Bool where cast = bounds (-1 / 0) (1 / 0)

instance Connection 'L Int8 Word8 where cast = i08w08

instance Connection 'L Word8 Word16 where cast = w08w16
instance Connection 'L Int8 Word16 where cast = i08w16
instance Connection 'L Int16 Word16 where cast = i16w16

instance Connection 'L Word8 Word32 where cast = w08w32
instance Connection 'L Word16 Word32 where cast = w16w32
instance Connection 'L Int8 Word32 where cast = i08w32
instance Connection 'L Int16 Word32 where cast = i16w32
instance Connection 'L Int32 Word32 where cast = i32w32

instance Connection 'L Word8 Word64 where cast = w08w64
instance Connection 'L Word16 Word64 where cast = w16w64
instance Connection 'L Word32 Word64 where cast = w32w64
instance Connection 'L Int8 Word64 where cast = i08w64
instance Connection 'L Int16 Word64 where cast = i16w64
instance Connection 'L Int32 Word64 where cast = i32w64
instance Connection 'L Int64 Word64 where cast = i64w64
instance Connection 'L Int Word64 where cast = ixxw64

instance Connection 'L Word8 Word where cast = w08wxx
instance Connection 'L Word16 Word where cast = w16wxx
instance Connection 'L Word32 Word where cast = w32wxx
instance Connection k Word64 Word where cast = w64wxx
instance Connection 'L Int8 Word where cast = i08wxx
instance Connection 'L Int16 Word where cast = i16wxx
instance Connection 'L Int32 Word where cast = i32wxx
instance Connection 'L Int64 Word where cast = i64wxx
instance Connection 'L Int Word where cast = ixxwxx

instance Connection 'L Word8 Natural where cast = w08nat
instance Connection 'L Word16 Natural where cast = w16nat
instance Connection 'L Word32 Natural where cast = w32nat
instance Connection 'L Word64 Natural where cast = w64nat
instance Connection 'L Word Natural where cast = wxxnat
instance Connection 'L Int8 Natural where cast = i08nat
instance Connection 'L Int16 Natural where cast = i16nat
instance Connection 'L Int32 Natural where cast = i32nat
instance Connection 'L Int64 Natural where cast = i64nat
instance Connection 'L Int Natural where cast = ixxnat
instance Connection 'L Integer Natural where cast = intnat

instance Connection k Uni Integer where cast = f00int

instance Connection k Deci Uni where cast = f01f00
instance Connection k Centi Uni where cast = f02f00
instance Connection k Milli Uni where cast = f03f00
instance Connection k Micro Uni where cast = f06f00
instance Connection k Nano Uni where cast = f09f00
instance Connection k Pico Uni where cast = f12f00

instance Connection k Centi Deci where cast = f02f01
instance Connection k Milli Deci where cast = f03f01
instance Connection k Micro Deci where cast = f06f01
instance Connection k Nano Deci where cast = f09f01
instance Connection k Pico Deci where cast = f12f01

instance Connection k Milli Centi where cast = f03f02
instance Connection k Micro Centi where cast = f06f02
instance Connection k Nano Centi where cast = f09f02
instance Connection k Pico Centi where cast = f12f02

instance Connection k Micro Milli where cast = f06f03
instance Connection k Nano Milli where cast = f09f03
instance Connection k Pico Milli where cast = f12f03

instance Connection k Nano Micro where cast = f09f06
instance Connection k Pico Micro where cast = f12f06

instance Connection k Pico Nano where cast = f12f09

instance Connection k Double Float where cast = f64f32
instance Connection k Rational Float where cast = ratf32

instance Connection k Rational Double where cast = ratf64

instance Connection 'L Word8 (Maybe Int16) where cast = w08i16
instance Connection 'L Int8 (Maybe Int16) where cast = i08i16

instance Connection 'L Word8 (Maybe Int32) where cast = w08i32
instance Connection 'L Word16 (Maybe Int32) where cast = w16i32
instance Connection 'L Int8 (Maybe Int32) where cast = i08i32
instance Connection 'L Int16 (Maybe Int32) where cast = i16i32

instance Connection 'L Word8 (Maybe Int64) where cast = w08i64
instance Connection 'L Word16 (Maybe Int64) where cast = w16i64
instance Connection 'L Word32 (Maybe Int64) where cast = w32i64
instance Connection 'L Int8 (Maybe Int64) where cast = i08i64
instance Connection 'L Int16 (Maybe Int64) where cast = i16i64
instance Connection 'L Int32 (Maybe Int64) where cast = i32i64

instance Connection 'L Word8 (Maybe Int) where cast = w08ixx
instance Connection 'L Word16 (Maybe Int) where cast = w16ixx
instance Connection 'L Word32 (Maybe Int) where cast = w32ixx
instance Connection 'L Int8 (Maybe Int) where cast = i08ixx
instance Connection 'L Int16 (Maybe Int) where cast = i16ixx
instance Connection 'L Int32 (Maybe Int) where cast = i32ixx
instance Connection k Int64 Int where cast = i64ixx
instance Connection k SystemTime Int where cast = sysixx

instance Connection 'L Word8 (Maybe Integer) where cast = w08int
instance Connection 'L Word16 (Maybe Integer) where cast = w16int
instance Connection 'L Word32 (Maybe Integer) where cast = w32int
instance Connection 'L Word64 (Maybe Integer) where cast = w64int
instance Connection 'L Word (Maybe Integer) where cast = wxxint
instance Connection 'L Natural (Maybe Integer) where cast = natint

instance Connection 'L Int8 (Maybe Integer) where cast = i08int
instance Connection 'L Int16 (Maybe Integer) where cast = i16int
instance Connection 'L Int32 (Maybe Integer) where cast = i32int
instance Connection 'L Int64 (Maybe Integer) where cast = i64int
instance Connection 'L Int (Maybe Integer) where cast = ixxint

instance Connection 'L Integer (Maybe Integer) where
    -- | 
    --
    -- NB: This instance is provided for use with 'fromInteger'.
    -- It is lawful for /abs i <= maxBound @Int64/
    cast = c1 >>> intnat >>> natint >>> c2
      where
        c1 = Cast shiftR shiftL shiftR
        c2 = Cast (fmap shiftL) (fmap shiftR) (fmap shiftL)

        shiftR x = x + m
        shiftL x = x - m
        m = 9223372036854775808

instance Connection k Rational (Extended Word8) where cast = ratw08
instance Connection k Rational (Extended Word16) where cast = ratw16
instance Connection k Rational (Extended Word32) where cast = ratw32
instance Connection k Rational (Extended Word64) where cast = ratw64
instance Connection k Rational (Extended Word) where cast = ratwxx
instance Connection k Rational (Extended Natural) where cast = ratnat

instance Connection k Rational (Extended Int8) where cast = rati08
instance Connection k Rational (Extended Int16) where cast = rati16
instance Connection k Rational (Extended Int32) where cast = rati32
instance Connection k Rational (Extended Int64) where cast = rati64
instance Connection k Rational (Extended Int) where cast = ratixx
instance Connection k Rational (Extended Integer) where cast = ratint
instance Connection k Rational (Extended SystemTime) where cast = ratsys
instance HasResolution res => Connection k Rational (Extended (Fixed res)) where cast = ratfix

instance Connection k Float (Extended Word8) where cast = f32w08
instance Connection k Float (Extended Word16) where cast = f32w16
instance Connection 'L Float (Extended Word32) where cast = f32w32
instance Connection 'L Float (Extended Word64) where cast = f32w64
instance Connection 'L Float (Extended Word) where cast = f32wxx
instance Connection 'L Float (Extended Natural) where cast = f32nat

instance Connection k Float (Extended Int8) where cast = f32i08
instance Connection k Float (Extended Int16) where cast = f32i16
instance Connection 'L Float (Extended Int32) where cast = f32i32
instance Connection 'L Float (Extended Int64) where cast = f32i64
instance Connection 'L Float (Extended Int) where cast = f32ixx
instance Connection 'L Float (Extended Integer) where cast = f32int
instance HasResolution res => Connection 'L Float (Extended (Fixed res)) where cast = f32fix

instance Connection k Double (Extended Word8) where cast = f64w08
instance Connection k Double (Extended Word16) where cast = f64w16
instance Connection k Double (Extended Word32) where cast = f64w32
instance Connection 'L Double (Extended Word64) where cast = f64w64
instance Connection 'L Double (Extended Word) where cast = f64wxx
instance Connection 'L Double (Extended Natural) where cast = f64nat

instance Connection k Double (Extended Int8) where cast = f64i08
instance Connection k Double (Extended Int16) where cast = f64i16
instance Connection k Double (Extended Int32) where cast = f64i32
instance Connection 'L Double (Extended Int64) where cast = f64i64
instance Connection 'L Double (Extended Int) where cast = f64ixx
instance Connection 'L Double (Extended Integer) where cast = f64int

instance HasResolution res => Connection 'L Double (Extended (Fixed res)) where cast = f64fix

instance Connection k a b => Connection k (Identity a) b where
    cast = Cast runIdentity Identity runIdentity >>> cast

instance Connection k a b => Connection k a (Identity b) where
    cast = cast >>> Cast Identity runIdentity Identity

-- Internal

-------------------------

bounds' :: (Eq a, Bounded a) => Cast k a Bool
bounds' = bounds minBound maxBound

bounds :: Eq a => a -> a -> Cast k a Bool
bounds x y = Cast f g h
  where
    g False = x
    g True = y

    f i
        | i == x = False
        | otherwise = True

    h i
        | i == y = True
        | otherwise = False
