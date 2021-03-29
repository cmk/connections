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
import safe Data.Bool (bool)
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
import safe Prelude hiding (floor, ceiling, round, truncate, fromInteger, fromRational)

-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import GHC.Real (Ratio(..))
-- >>> import Data.IntSet (IntSet,fromList)
-- >>> :load Data.Connection
-- >>> import Prelude hiding (round, floor, ceiling, truncate)

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
class (Preorder a, Preorder b) => Connection k a b where
    -- |
    --
    -- >>> outer (conn @_ @Rational @Float) (22 :% 7)
    -- (3.142857,3.1428573)
    -- >>> outer (conn @_ @Double @Float) pi
    -- (3.1415925,3.1415927)
    conn :: Conn k a b

type Left = Connection 'L

-- | A specialization of /conn/ to left-side connections.
--
left :: Left a b => ConnL a b
left = conn @ 'L

type Right = Connection 'R

-- | A specialization of /conn/ to right-side connections.
--
right :: Right a b => ConnR a b
right = conn @ 'R

-- | A constraint kind representing an <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
type Triple a b = (Left a b, Right a b)

-- | A constraint kind for 'Integer' conversions.
type ConnInteger a = Left a (Maybe Integer)

-- | A replacement for the version in /base/.
--
--  Usable in conjunction with /RebindableSyntax/:
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = upper conn . Just

-- | A constraint kind for 'Rational' conversions.
type ConnRational a = Triple Rational a

-- | A replacement for the version in /base/.
--
-- Usable in conjunction with /RebindableSyntax/:
--
fromRational :: forall a. ConnRational a => Rational -> a
fromRational x = case pcompare r l of
    Just GT -> ceiling left x
    Just LT -> floor right x
    _ -> if x >~ 0 then ceiling left x else floor right x
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
    -- | Supplied for use with /RebindableSyntax/
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
instance Connection k Float (Extended Int8) where conn = f32i08
instance Connection k Float (Extended Int16) where conn = f32i16
instance Connection 'L Float (Extended SystemTime) where conn = f32sys
instance HasResolution res => Connection 'L Float (Extended (Fixed res)) where conn = connL ratf32 >>> ratfix


instance Connection k Double (Extended Word8) where conn = f64w08
instance Connection k Double (Extended Word16) where conn = f64w16
instance Connection k Double (Extended Word32) where conn = f64w32
instance Connection k Double (Extended Int8) where conn = f64i08
instance Connection k Double (Extended Int16) where conn = f64i16
instance Connection k Double (Extended Int32) where conn = f64i32
instance Connection 'L Double (Extended SystemTime) where conn = f64sys
instance HasResolution res => Connection 'L Double (Extended (Fixed res)) where conn = connL ratf64 >>> ratfix

instance Connection k a b => Connection k (Identity a) b where
    conn = Conn runIdentity Identity runIdentity >>> conn

instance Connection k a b => Connection k a (Identity b) where
    conn = conn >>> Conn Identity runIdentity Identity

{-
instance (Triple () a, Triple () b) => Connection k () (a, b) where
    conn = Conn (const (minimal, minimal)) (const ()) (const (maximal, maximal))

instance Preorder a => Connection 'L () (Maybe a) where
    conn = ConnL (const Nothing) (const ())

instance Right () a => Connection 'R () (Maybe a) where
    conn = ConnR (const ()) (const $ Just maximal)

instance Preorder a => Connection k () (Extended a) where
    conn = Conn (const NegInf) (const ()) (const PosInf)

instance (Left () a, Preorder b) => Connection 'L () (Either a b) where
    conn = ConnL (const $ Left minimal) (const ())

instance (Preorder a, Right () b) => Connection 'R () (Either a b) where
    conn = ConnR (const ()) (const $ Right maximal)

instance (Preorder a, Right b Bool) => Connection k (Maybe a) (Either a b) where
    conn = maybeR right
instance (Left a Bool, Preorder b) => Connection k (Maybe b) (Either a b) where
    conn = maybeL left
-}

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

{-
instance (Triple (a, a) a, Triple (b, b) b) => Connection k ((a, b), (a, b)) (a, b) where
  conn = Conn (uncurry joinTuple) fork (uncurry meetTuple)

instance Left (a, a) a => Connection 'L (Maybe a, Maybe a) (Maybe a) where
  conn = ConnL (uncurry joinMaybe) fork

instance Right (a, a) a => Connection 'R (Maybe a, Maybe a) (Maybe a) where
  conn = ConnR fork (uncurry meetMaybe)

instance Left (a, a) a => Connection 'L (Extended a, Extended a) (Extended a) where
  conn = ConnL (uncurry joinExtended) fork

instance Right (a, a) a => Connection 'R (Extended a, Extended a) (Extended a) where
  conn = ConnR fork (uncurry meetExtended)

-- | All minimal elements of the upper lattice cover all maximal elements of the lower lattice.
instance (Left (a, a) a, Left (b, b) b) => Connection 'L (Either a b, Either a b) (Either a b) where
  conn = ConnL (uncurry joinEither) fork

instance (Right (a, a) a, Right (b, b) b) => Connection 'R (Either a b, Either a b) (Either a b) where
  conn = ConnR fork (uncurry meetEither)

joinMaybe :: Connection 'L (a, a) a => Maybe a -> Maybe a -> Maybe a
joinMaybe (Just x) (Just y) = Just (x `join` y)
joinMaybe u@(Just _) _ = u
joinMaybe _ u@(Just _) = u
joinMaybe Nothing Nothing = Nothing

meetMaybe :: Right (a, a) a => Maybe a -> Maybe a -> Maybe a
meetMaybe Nothing Nothing = Nothing
meetMaybe Nothing _ = Nothing
meetMaybe _ Nothing = Nothing
meetMaybe (Just x) (Just y) = Just (x `meet` y)

joinExtended :: Connection 'L (a, a) a => Extended a -> Extended a -> Extended a
joinExtended PosInf          _            = PosInf
joinExtended _            PosInf          = PosInf
joinExtended (Extended x) (Extended y) = Extended (x `join` y)
joinExtended NegInf       y            = y
joinExtended x            NegInf       = x

meetExtended :: Right (a, a) a => Extended a -> Extended a -> Extended a
meetExtended PosInf          y            = y
meetExtended x            PosInf          = x
meetExtended (Extended x) (Extended y) = Extended (x `meet` y)
meetExtended NegInf       _            = NegInf
meetExtended _            NegInf       = NegInf

joinEither :: (Connection 'L (a, a) a, Connection 'L (b, b) b) => Either a b -> Either a b -> Either a b
joinEither (Right x) (Right y) = Right (x `join` y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x `join` y)

meetEither :: (Right (a, a) a, Right (b, b) b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x `meet` y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x `meet` y)

joinTuple :: (Connection 'L (a, a) a, Connection 'L (b, b) b) => (a, b) -> (a, b) -> (a, b)
joinTuple (x1, y1) (x2, y2) = (x1 `join` x2, y1 `join` y2)

meetTuple :: (Right (a, a) a, Right (b, b) b) => (a, b) -> (a, b) -> (a, b)
meetTuple (x1, y1) (x2, y2) = (x1 `meet` x2, y1 `meet` y2)
-}
