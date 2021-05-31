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
    Left,
    left,
    Right,
    right,
    Triple,
    ConnInteger,
    fromInteger,
    ConnRational,
    fromRational,
    Connection (..),
) where

import safe Control.Category ((>>>))
import safe Data.Connection.Conn
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

-- | A < https://ncatlab.org/nlab/show/adjoint+string chain > of Galois connections of length 2 or 3.
class (Preorder a, Preorder b) => Connection k a b where
    
    conn :: Conn k a b

type Left = Connection 'L

-- | A specialization of /conn/ to left-side connections.
left :: Left a b => ConnL a b
left = conn @ 'L

type Right = Connection 'R

-- | A specialization of /conn/ to right-side connections.
right :: Right a b => ConnR a b
right = conn @ 'R

-- | A constraint kind representing an <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
type Triple a b = (Left a b, Right a b)

-- | A constraint kind for 'Integer' conversions.
type ConnInteger a = Left a (Maybe Integer)

-- | A replacement for the version in /base/.
--
--  Usable in conjunction with /RebindableSyntax/:
fromInteger :: ConnInteger a => Integer -> a
fromInteger = upper conn . Just

-- | A constraint kind for 'Rational' conversions.
type ConnRational a = Triple Rational a

-- | A replacement for the version in /base/.
--
-- Usable in conjunction with /RebindableSyntax/:
fromRational :: forall a. ConnRational a => Rational -> a
fromRational x = case pcompare r l of
    Just GT -> ceiling left x
    Just LT -> floor right x
    _ -> if x >~ 0 then floor right x else ceiling left x
  where
    r = x - lower1 (right @Rational @a) id x -- dist from lower bound
    l = upper1 (left @Rational @a) id x - x -- dist from upper bound
{-# INLINE fromRational #-}

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Preorder a => Connection k a a where conn = identity

instance Connection k Ordering Bool where conn = bounds'
instance Connection k Word8 Bool where conn = bounds'
instance Connection k Word16 Bool where conn = bounds'
instance Connection k Word32 Bool where conn = bounds'
instance Connection k Word64 Bool where conn = bounds'
instance Connection k Word Bool where conn = bounds'
instance Connection k Int8 Bool where conn = bounds'
instance Connection k Int16 Bool where conn = bounds'
instance Connection k Int32 Bool where conn = bounds'
instance Connection k Int64 Bool where conn = bounds'
instance Connection k Int Bool where conn = bounds'
instance Connection k Rational Bool where conn = bounds (-1 :% 0) (1 :% 0)
instance Connection k Float Bool where conn = bounds (-1 / 0) (1 / 0)
instance Connection k Double Bool where conn = bounds (-1 / 0) (1 / 0)

instance Connection 'L Int8 Word8 where conn = i08w08

instance Connection 'L Word8 Word16 where conn = w08w16
instance Connection 'L Int8 Word16 where conn = i08w16
instance Connection 'L Int16 Word16 where conn = i16w16

instance Connection 'L Word8 Word32 where conn = w08w32
instance Connection 'L Word16 Word32 where conn = w16w32
instance Connection 'L Int8 Word32 where conn = i08w32
instance Connection 'L Int16 Word32 where conn = i16w32
instance Connection 'L Int32 Word32 where conn = i32w32

instance Connection 'L Word8 Word64 where conn = w08w64
instance Connection 'L Word16 Word64 where conn = w16w64
instance Connection 'L Word32 Word64 where conn = w32w64
instance Connection 'L Int8 Word64 where conn = i08w64
instance Connection 'L Int16 Word64 where conn = i16w64
instance Connection 'L Int32 Word64 where conn = i32w64
instance Connection 'L Int64 Word64 where conn = i64w64
instance Connection 'L Int Word64 where conn = ixxw64

instance Connection 'L Word8 Word where conn = w08wxx
instance Connection 'L Word16 Word where conn = w16wxx
instance Connection 'L Word32 Word where conn = w32wxx
instance Connection k Word64 Word where conn = w64wxx
instance Connection 'L Int8 Word where conn = i08wxx
instance Connection 'L Int16 Word where conn = i16wxx
instance Connection 'L Int32 Word where conn = i32wxx
instance Connection 'L Int64 Word where conn = i64wxx
instance Connection 'L Int Word where conn = ixxwxx

instance Connection 'L Word8 Natural where conn = w08nat
instance Connection 'L Word16 Natural where conn = w16nat
instance Connection 'L Word32 Natural where conn = w32nat
instance Connection 'L Word64 Natural where conn = w64nat
instance Connection 'L Word Natural where conn = wxxnat
instance Connection 'L Int8 Natural where conn = i08nat
instance Connection 'L Int16 Natural where conn = i16nat
instance Connection 'L Int32 Natural where conn = i32nat
instance Connection 'L Int64 Natural where conn = i64nat
instance Connection 'L Int Natural where conn = ixxnat
instance Connection 'L Integer Natural where conn = intnat

instance Connection k Uni Integer where conn = f00int

instance Connection k Deci Uni where conn = f01f00
instance Connection k Centi Uni where conn = f02f00
instance Connection k Milli Uni where conn = f03f00
instance Connection k Micro Uni where conn = f06f00
instance Connection k Nano Uni where conn = f09f00
instance Connection k Pico Uni where conn = f12f00

instance Connection k Centi Deci where conn = f02f01
instance Connection k Milli Deci where conn = f03f01
instance Connection k Micro Deci where conn = f06f01
instance Connection k Nano Deci where conn = f09f01
instance Connection k Pico Deci where conn = f12f01

instance Connection k Milli Centi where conn = f03f02
instance Connection k Micro Centi where conn = f06f02
instance Connection k Nano Centi where conn = f09f02
instance Connection k Pico Centi where conn = f12f02

instance Connection k Micro Milli where conn = f06f03
instance Connection k Nano Milli where conn = f09f03
instance Connection k Pico Milli where conn = f12f03

instance Connection k Nano Micro where conn = f09f06
instance Connection k Pico Micro where conn = f12f06

instance Connection k Pico Nano where conn = f12f09

instance Connection k Double Float where conn = f64f32
instance Connection k Rational Float where conn = ratf32

instance Connection k Rational Double where conn = ratf64

instance Connection 'L Word8 (Maybe Int16) where conn = w08i16
instance Connection 'L Int8 (Maybe Int16) where conn = i08i16

instance Connection 'L Word8 (Maybe Int32) where conn = w08i32
instance Connection 'L Word16 (Maybe Int32) where conn = w16i32
instance Connection 'L Int8 (Maybe Int32) where conn = i08i32
instance Connection 'L Int16 (Maybe Int32) where conn = i16i32

instance Connection 'L Word8 (Maybe Int64) where conn = w08i64
instance Connection 'L Word16 (Maybe Int64) where conn = w16i64
instance Connection 'L Word32 (Maybe Int64) where conn = w32i64
instance Connection 'L Int8 (Maybe Int64) where conn = i08i64
instance Connection 'L Int16 (Maybe Int64) where conn = i16i64
instance Connection 'L Int32 (Maybe Int64) where conn = i32i64

instance Connection 'L Word8 (Maybe Int) where conn = w08ixx
instance Connection 'L Word16 (Maybe Int) where conn = w16ixx
instance Connection 'L Word32 (Maybe Int) where conn = w32ixx
instance Connection 'L Int8 (Maybe Int) where conn = i08ixx
instance Connection 'L Int16 (Maybe Int) where conn = i16ixx
instance Connection 'L Int32 (Maybe Int) where conn = i32ixx
instance Connection k Int64 Int where conn = i64ixx
instance Connection k SystemTime Int where conn = sysixx

instance Connection 'L Word8 (Maybe Integer) where conn = w08int
instance Connection 'L Word16 (Maybe Integer) where conn = w16int
instance Connection 'L Word32 (Maybe Integer) where conn = w32int
instance Connection 'L Word64 (Maybe Integer) where conn = w64int
instance Connection 'L Word (Maybe Integer) where conn = wxxint
instance Connection 'L Natural (Maybe Integer) where conn = natint

instance Connection 'L Int8 (Maybe Integer) where conn = i08int
instance Connection 'L Int16 (Maybe Integer) where conn = i16int
instance Connection 'L Int32 (Maybe Integer) where conn = i32int
instance Connection 'L Int64 (Maybe Integer) where conn = i64int
instance Connection 'L Int (Maybe Integer) where conn = ixxint

instance Connection 'L Integer (Maybe Integer) where
    -- | 
    --
    -- NB: This instance is provided for use with 'fromInteger'.
    -- It is lawful for /abs i <= maxBound @Int64/
    conn = c1 >>> intnat >>> natint >>> c2
      where
        c1 = Conn shiftR shiftL shiftR
        c2 = Conn (fmap shiftL) (fmap shiftR) (fmap shiftL)

        shiftR x = x + m
        shiftL x = x - m
        m = 9223372036854775808

instance Connection k Rational (Extended Word8) where conn = ratw08
instance Connection k Rational (Extended Word16) where conn = ratw16
instance Connection k Rational (Extended Word32) where conn = ratw32
instance Connection k Rational (Extended Word64) where conn = ratw64
instance Connection k Rational (Extended Word) where conn = ratwxx
instance Connection k Rational (Extended Natural) where conn = ratnat

instance Connection k Rational (Extended Int8) where conn = rati08
instance Connection k Rational (Extended Int16) where conn = rati16
instance Connection k Rational (Extended Int32) where conn = rati32
instance Connection k Rational (Extended Int64) where conn = rati64
instance Connection k Rational (Extended Int) where conn = ratixx
instance Connection k Rational (Extended Integer) where conn = ratint
instance Connection k Rational (Extended SystemTime) where conn = ratsys
instance HasResolution res => Connection k Rational (Extended (Fixed res)) where conn = ratfix

instance Connection k Float (Extended Word8) where conn = f32w08
instance Connection k Float (Extended Word16) where conn = f32w16
instance Connection 'L Float (Extended Word32) where conn = f32w32
instance Connection 'L Float (Extended Word64) where conn = f32w64
instance Connection 'L Float (Extended Word) where conn = f32wxx
instance Connection 'L Float (Extended Natural) where conn = f32nat

instance Connection k Float (Extended Int8) where conn = f32i08
instance Connection k Float (Extended Int16) where conn = f32i16
instance Connection 'L Float (Extended Int32) where conn = f32i32
instance Connection 'L Float (Extended Int64) where conn = f32i64
instance Connection 'L Float (Extended Int) where conn = f32ixx
instance Connection 'L Float (Extended Integer) where conn = f32int
instance HasResolution res => Connection 'L Float (Extended (Fixed res)) where conn = f32fix

instance Connection k Double (Extended Word8) where conn = f64w08
instance Connection k Double (Extended Word16) where conn = f64w16
instance Connection k Double (Extended Word32) where conn = f64w32
instance Connection 'L Double (Extended Word64) where conn = f64w64
instance Connection 'L Double (Extended Word) where conn = f64wxx
instance Connection 'L Double (Extended Natural) where conn = f64nat

instance Connection k Double (Extended Int8) where conn = f64i08
instance Connection k Double (Extended Int16) where conn = f64i16
instance Connection k Double (Extended Int32) where conn = f64i32
instance Connection 'L Double (Extended Int64) where conn = f64i64
instance Connection 'L Double (Extended Int) where conn = f64ixx
instance Connection 'L Double (Extended Integer) where conn = f64int

instance HasResolution res => Connection 'L Double (Extended (Fixed res)) where conn = f64fix

instance Connection k a b => Connection k (Identity a) b where
    conn = Conn runIdentity Identity runIdentity >>> conn

instance Connection k a b => Connection k a (Identity b) where
    conn = conn >>> Conn Identity runIdentity Identity

-- Internal

-------------------------

bounds' :: (Eq a, Bounded a) => Conn k a Bool
bounds' = bounds minBound maxBound

bounds :: Eq a => a -> a -> Conn k a Bool
bounds x y = Conn f g h
  where
    g False = x
    g True = y

    f i
        | i == x = False
        | otherwise = True

    h i
        | i == y = True
        | otherwise = False
