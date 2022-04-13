{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Connection.Class (
    castL,
    castR,
    Connection (..),
) where

import Data.Connection.Cast
import Data.Connection.Fixed
import Data.Connection.Float
import Data.Connection.Int
import Data.Connection.Ratio
import Data.Connection.Time
import Data.Connection.Word
import Data.Int
import Data.Word
import Numeric.Natural

castL :: Connection 'L a b => Cast 'L a b
castL = cast @'L

castR :: Connection 'R a b => Cast 'R a b
castR = cast @'R

-- | A < https://ncatlab.org/nlab/show/adjoint+string chain > of Galois connections of length 2 or 3.
class Connection (k :: Side) a b where
    cast :: Cast k a b

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Connection k a a where cast = identity

instance Connection k Ordering Bool where cast = bndbin
instance Connection k Word8 Bool where cast = bndbin
instance Connection k Word16 Bool where cast = bndbin
instance Connection k Word32 Bool where cast = bndbin
instance Connection k Word64 Bool where cast = bndbin
instance Connection k Word Bool where cast = bndbin
instance Connection k Int8 Bool where cast = bndbin
instance Connection k Int16 Bool where cast = bndbin
instance Connection k Int32 Bool where cast = bndbin
instance Connection k Int64 Bool where cast = bndbin
instance Connection k Int Bool where cast = bndbin

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
instance Connection k Word Word64 where cast = wxxw64
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

instance Connection k (Extended Word8) Int16 where cast = w08i16
instance Connection k (Extended Int8) Int16 where cast = i08i16

instance Connection k (Extended Word8) Int32 where cast = w08i32
instance Connection k (Extended Word16) Int32 where cast = w16i32
instance Connection k (Extended Int8) Int32 where cast = i08i32
instance Connection k (Extended Int16) Int32 where cast = i16i32

instance Connection k (Extended Word8) Int64 where cast = w08i64
instance Connection k (Extended Word16) Int64 where cast = w16i64
instance Connection k (Extended Word32) Int64 where cast = w32i64
instance Connection k (Extended Int8) Int64 where cast = i08i64
instance Connection k (Extended Int16) Int64 where cast = i16i64
instance Connection k (Extended Int32) Int64 where cast = i32i64
instance Connection k Int Int64 where cast = ixxi64

instance Connection k (Extended Word8) Int where cast = w08ixx
instance Connection k (Extended Word16) Int where cast = w16ixx
instance Connection k (Extended Word32) Int where cast = w32ixx
instance Connection k (Extended Int8) Int where cast = i08ixx
instance Connection k (Extended Int16) Int where cast = i16ixx
instance Connection k (Extended Int32) Int where cast = i32ixx
instance Connection k Int64 Int where cast = i64ixx
instance Connection k SystemTime Int where cast = sysixx

instance Connection 'L (Extended Word8) (Maybe Integer) where cast = w08int
instance Connection 'L (Extended Word16) (Maybe Integer) where cast = w16int
instance Connection 'L (Extended Word32) (Maybe Integer) where cast = w32int
instance Connection 'L (Extended Word64) (Maybe Integer) where cast = w64int
instance Connection 'L (Extended Word) (Maybe Integer) where cast = wxxint

instance Connection 'L (Extended Int8) (Maybe Integer) where cast = i08int
instance Connection 'L (Extended Int16) (Maybe Integer) where cast = i16int
instance Connection 'L (Extended Int32) (Maybe Integer) where cast = i32int
instance Connection 'L (Extended Int64) (Maybe Integer) where cast = i64int
instance Connection 'L (Extended Int) (Maybe Integer) where cast = ixxint

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
instance Connection 'L Float (Extended SystemTime) where cast = f32sys

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
instance Connection 'L Double (Extended SystemTime) where cast = f64sys

instance HasResolution res => Connection 'L Double (Extended (Fixed res)) where cast = f64fix
