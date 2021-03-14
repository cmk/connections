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
    -- * Types
    Left,
    left,
    Right,
    right,
    Triple,

    -- * Lattices
    (\/),
    (/\),
    lub,
    glb,
    choose,
    divide,
    minimal,
    maximal,
    extremal,

    -- * Connection
    Connection (..),

    -- ** RebindableSyntax
    ConnInteger,
    ConnRational,
) where

import safe Control.Category ((>>>))
import safe Data.Bool (bool)
import safe Data.Connection.Conn
import safe Data.Connection.Fixed
import safe Data.Connection.Float
import safe Data.Connection.Int
import safe Data.Connection.Ratio
import safe Data.Connection.Word
import safe Data.Functor.Identity
import safe Data.Int
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe Data.Order
import safe Data.Order.Extended
import safe qualified Data.Set as Set
import safe Data.Word
import safe Numeric.Natural
import safe Prelude hiding (ceiling, floor, round, truncate)

-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import GHC.Real (Ratio(..))
-- >>> import Data.Set (Set,fromList)
-- >>> :load Data.Connection
-- >>> import Prelude hiding (round, floor, ceiling, truncate)

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
--
--  Usable in conjunction with /RebindableSyntax/:
--
--  > fromInteger = upper conn . Just :: ConnInteger a => Integer -> a
type ConnInteger a = Left a (Maybe Integer)

-- | A constraint kind for 'Rational' conversions.
--
-- Usable in conjunction with /RebindableSyntax/:
--
--  > fromRational = round conn :: ConnRational a => Rational -> a
type ConnRational a = Triple Rational a

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
class (Preorder a, Preorder b) => Connection k a b where
    -- |
    --
    -- >>> range (conn @_ @Rational @Float) (22 :% 7)
    -- (3.142857,3.1428573)
    -- >>> range (conn @_ @Double @Float) pi
    -- (3.1415925,3.1415927)
    conn :: Conn k a b


---------------------------------------------------------------------
-- Lattices
---------------------------------------------------------------------

infixr 5 \/

-- | Lattice join.
--
-- > (\/) = curry $ lower semilattice
(\/) :: Left (a, a) a => a -> a -> a
(\/) = join conn

infixr 6 /\ -- comment for the parser

-- | Lattice meet.
--
-- > (/\) = curry $ floor semilattice
(/\) :: Right (a, a) a => a -> a -> a
(/\) = meet conn

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
lub :: Triple (a, a) a => a -> a -> a -> a
lub x y z = x /\ y \/ y /\ z \/ z /\ x

-- | Greatest lower bound operator.
--
-- > glb x x y = x
-- > glb x y z = glb z x y
-- > glb x y z = glb x z y
-- > glb (glb x w y) w z = glb x w (glb y w z)
--
-- >>> glb 1.0 9.0 7.0
-- 7.0
-- >>> glb 1.0 9.0 (0.0 / 0.0)
-- 9.0
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
glb :: Triple (a, a) a => a -> a -> a -> a
glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

infixr 3 `choose`

-- | A preorder variant of 'Control.Arrow.|||'.
choose :: Conn k c a -> Conn k c b -> Conn k c (Either a b)
choose f g = Conn Left (either id id) Right >>> f `choice` g

infixr 4 `divide`

-- | A preorder variant of 'Control.Arrow.&&&'.
divide :: Connection k (c, c) c => Conn k a c -> Conn k b c -> Conn k (a, b) c
divide f g = f `strong` g >>> conn

-- | A minimal element of a preorder.
--
-- > x /\ minimal = minimal
-- > x \/ minimal = x
--
-- 'minimal' needn't be unique, but it must obey:
--
-- > x <~ minimal => x ~~ minimal
minimal :: Left () a => a
minimal = ceiling conn ()

-- | A maximal element of a preorder.
--
-- > x /\ maximal = x
-- > x \/ maximal = maximal
--
-- 'maximal' needn't be unique, but it must obey:
--
-- > x >~ maximal => x ~~ maximal
maximal :: Right () a => a
maximal = floor conn ()

-- | The canonical connection with a 'Bool'.
extremal :: Triple () a => Conn k a Bool
extremal = Conn f g h
  where
    g False = minimal
    g True = maximal

    f i
        | i ~~ minimal = False
        | otherwise = True

    h i
        | i ~~ maximal = True
        | otherwise = False

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Preorder a => Connection k a a where conn = identity

instance Connection k ((), ()) () where conn = latticeOrd

instance Connection k () Bool where conn = bounded
instance Connection k Ordering Bool where conn = extremal
instance Connection k Word8 Bool where conn = extremal
instance Connection k Word16 Bool where conn = extremal
instance Connection k Word32 Bool where conn = extremal
instance Connection k Word64 Bool where conn = extremal
instance Connection k Word Bool where conn = extremal
instance Connection k Positive Bool where conn = extremal
instance Connection k Int8 Bool where conn = extremal
instance Connection k Int16 Bool where conn = extremal
instance Connection k Int32 Bool where conn = extremal
instance Connection k Int64 Bool where conn = extremal
instance Connection k Int Bool where conn = extremal
instance Connection k Rational Bool where conn = extremal
instance Connection k Float Bool where conn = extremal
instance Connection k Double Bool where conn = extremal
instance Connection k (Bool, Bool) Bool where conn = latticeOrd

instance Connection k () Ordering where conn = bounded
instance Connection k (Ordering, Ordering) Ordering where conn = latticeOrd

instance Connection k () Word8 where conn = bounded
instance Connection 'L Int8 Word8 where conn = i08w08
instance Connection k (Word8, Word8) Word8 where conn = latticeOrd

instance Connection k () Word16 where conn = bounded
instance Connection 'L Word8 Word16 where conn = w08w16
instance Connection 'L Int8 Word16 where conn = i08w16
instance Connection 'L Int16 Word16 where conn = i16w16
instance Connection k (Word16, Word16) Word16 where conn = latticeOrd

instance Connection k () Word32 where conn = bounded
instance Connection 'L Word8 Word32 where conn = w08w32
instance Connection 'L Word16 Word32 where conn = w16w32
instance Connection 'L Int8 Word32 where conn = i08w32
instance Connection 'L Int16 Word32 where conn = i16w32
instance Connection 'L Int32 Word32 where conn = i32w32
instance Connection k (Word32, Word32) Word32 where conn = latticeOrd

instance Connection k () Word64 where conn = bounded
instance Connection 'L Word8 Word64 where conn = w08w64
instance Connection 'L Word16 Word64 where conn = w16w64
instance Connection 'L Word32 Word64 where conn = w32w64
instance Connection 'L Int8 Word64 where conn = i08w64
instance Connection 'L Int16 Word64 where conn = i16w64
instance Connection 'L Int32 Word64 where conn = i32w64
instance Connection 'L Int64 Word64 where conn = i64w64
instance Connection 'L Int Word64 where conn = ixxw64
instance Connection k (Word64, Word64) Word64 where conn = latticeOrd

instance Connection k () Word where conn = bounded
instance Connection 'L Word8 Word where conn = w08wxx
instance Connection 'L Word16 Word where conn = w16wxx
instance Connection 'L Word32 Word where conn = w32wxx
instance Connection k Word64 Word where conn = w64wxx
instance Connection 'L Int8 Word where conn = i08wxx
instance Connection 'L Int16 Word where conn = i16wxx
instance Connection 'L Int32 Word where conn = i32wxx
instance Connection 'L Int64 Word where conn = i64wxx
instance Connection 'L Int Word where conn = ixxwxx
instance Connection k (Word, Word) Word where conn = latticeOrd

instance Connection 'L () Natural where conn = ConnL (const 0) (const ())
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
instance Connection k (Natural, Natural) Natural where conn = latticeOrd

instance Connection k () Positive where
    conn = Conn (const $ 0 :% 1) (const ()) (const $ 1 :% 0)
instance Connection k (Positive, Positive) Positive where conn = latticeN5

instance Connection k () Int8 where conn = bounded
instance Connection k (Int8, Int8) Int8 where conn = latticeOrd
instance Connection k () Int16 where conn = bounded
instance Connection k (Int16, Int16) Int16 where conn = latticeOrd
instance Connection k () Int32 where conn = bounded
instance Connection k (Int32, Int32) Int32 where conn = latticeOrd
instance Connection k () Int64 where conn = bounded
instance Connection k (Int64, Int64) Int64 where conn = latticeOrd
instance Connection k () Int where conn = bounded
instance Connection k (Int, Int) Int where conn = latticeOrd
instance Connection k (Integer, Integer) Integer where conn = latticeOrd

instance Connection k () Rational where
    conn = Conn (const $ -1 :% 0) (const ()) (const $ 1 :% 0)
instance Connection k (Rational, Rational) Rational where conn = latticeN5

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

instance Connection k (Fixed e, Fixed e) (Fixed e) where conn = latticeOrd

instance Connection k () Float where conn = extremalN5
instance Connection k Double Float where conn = f64f32
instance Connection k Rational Float where conn = ratf32
instance Connection k (Float, Float) Float where conn = latticeN5

instance Connection k () Double where conn = extremalN5
instance Connection k Rational Double where conn = ratf64
instance Connection k (Double, Double) Double where conn = latticeN5

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
    conn = c1 >>> intnat >>> natint >>> c2
      where
        c1 = Conn shiftR shiftL shiftR
        c2 = Conn (fmap shiftL) (fmap shiftR) (fmap shiftL)

        shiftR x = x + m
        shiftL x = x - m
        m = 9223372036854775808

instance Connection k Rational (Extended Int8) where conn = rati08
instance Connection k Rational (Extended Int16) where conn = rati16
instance Connection k Rational (Extended Int32) where conn = rati32
instance Connection k Rational (Extended Int64) where conn = rati64
instance Connection k Rational (Extended Int) where conn = ratixx
instance Connection k Rational (Extended Integer) where conn = ratint
instance HasResolution prec => Connection k Rational (Extended (Fixed prec)) where conn = ratfix

instance Connection 'L Float (Extended Word8) where conn = f32i08 >>> mapped i08w08
instance Connection 'L Float (Extended Word16) where conn = f32i16 >>> mapped i16w16
instance Connection 'L Float (Extended Word32) where conn = f32i32 >>> mapped i32w32
instance Connection 'L Float (Extended Word64) where conn = f32i64 >>> mapped i64w64
instance Connection 'L Float (Extended Word) where conn = f32ixx >>> mapped ixxwxx
instance Connection 'L Float (Extended Natural) where conn = f32int >>> mapped intnat

-- | All 'Data.Int.Int8' values are exactly representable in a 'Float'.
instance Connection k Float (Extended Int8) where conn = f32i08

-- | All 'Data.Int.Int16' values are exactly representable in a 'Float'.
instance Connection k Float (Extended Int16) where conn = f32i16

instance Connection 'L Float (Extended Int32) where conn = f32i32
instance Connection 'L Float (Extended Int64) where conn = f32i64
instance Connection 'L Float (Extended Int) where conn = f32ixx
instance Connection 'L Float (Extended Integer) where conn = f32int
instance HasResolution res => Connection 'L Float (Extended (Fixed res)) where conn = connL ratf32 >>> ratfix

instance Connection 'L Double (Extended Word8) where conn = f64i08 >>> mapped i08w08
instance Connection 'L Double (Extended Word16) where conn = f64i16 >>> mapped i16w16
instance Connection 'L Double (Extended Word32) where conn = f64i32 >>> mapped i32w32
instance Connection 'L Double (Extended Word64) where conn = f64i64 >>> mapped i64w64
instance Connection 'L Double (Extended Word) where conn = f64ixx >>> mapped ixxwxx
instance Connection 'L Double (Extended Natural) where conn = f64int >>> mapped intnat

-- | All 'Data.Int.Int8' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int8) where conn = f64i08

-- | All 'Data.Int.Int16' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int16) where conn = f64i16

-- | All 'Data.Int.Int32' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int32) where conn = f64i32

instance Connection 'L Double (Extended Int64) where conn = f64i64
instance Connection 'L Double (Extended Int) where conn = f64ixx
instance Connection 'L Double (Extended Integer) where conn = f64int
instance HasResolution res => Connection 'L Double (Extended (Fixed res)) where conn = connL ratf64 >>> ratfix

instance Connection k a b => Connection k (Identity a) b where
    conn = Conn runIdentity Identity runIdentity >>> conn

instance Connection k a b => Connection k a (Identity b) where
    conn = conn >>> Conn Identity runIdentity Identity

instance (Triple () a, Triple () b) => Connection k () (a, b) where
    conn = Conn (const (minimal, minimal)) (const ()) (const (maximal, maximal))

instance Preorder a => Connection 'L () (Maybe a) where
    conn = ConnL (const Nothing) (const ())

instance Right () a => Connection 'R () (Maybe a) where
    conn = ConnR (const ()) (const $ Just maximal)

instance Preorder a => Connection k () (Extended a) where
    conn = Conn (const Bottom) (const ()) (const Top)

instance (Left () a, Preorder b) => Connection 'L () (Either a b) where
    conn = ConnL (const $ Left minimal) (const ())

instance (Preorder a, Right () b) => Connection 'R () (Either a b) where
    conn = ConnR (const ()) (const $ Right maximal)

instance (Preorder a, Triple () b) => Connection k (Maybe a) (Either a b) where
    conn = maybeL

instance (Triple () a, Preorder b) => Connection k (Maybe b) (Either a b) where
    conn = maybeR

instance (Total a) => Connection 'L () (Set.Set a) where
    conn = ConnL (const Set.empty) (const ())

instance Total a => Connection k (Set.Set a, Set.Set a) (Set.Set a) where
    conn = Conn (uncurry Set.union) fork (uncurry Set.intersection)

instance Connection 'L () IntSet.IntSet where
    conn = ConnL (const IntSet.empty) (const ())

instance Connection k (IntSet.IntSet, IntSet.IntSet) IntSet.IntSet where
    conn = Conn (uncurry IntSet.union) fork (uncurry IntSet.intersection)

instance (Total a, Preorder b) => Connection 'L () (Map.Map a b) where
    conn = ConnL (const Map.empty) (const ())

instance (Total a, Left (b, b) b) => Connection 'L (Map.Map a b, Map.Map a b) (Map.Map a b) where
    conn = ConnL (uncurry $ Map.unionWith (join conn)) fork

instance (Total a, Right (b, b) b) => Connection 'R (Map.Map a b, Map.Map a b) (Map.Map a b) where
    conn = ConnR fork (uncurry $ Map.intersectionWith (meet conn))

instance Preorder a => Connection 'L () (IntMap.IntMap a) where
    conn = ConnL (const IntMap.empty) (const ())

instance Left (a, a) a => Connection 'L (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    conn = ConnL (uncurry $ IntMap.unionWith (join conn)) fork

instance Right (a, a) a => Connection 'R (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    conn = ConnR fork (uncurry $ IntMap.intersectionWith (meet conn))

-- Internal

-------------------------

fork :: a -> (a, a)
fork x = (x, x)

bounded :: Bounded a => Conn k () a
bounded = Conn (const minBound) (const ()) (const maxBound)

latticeN5 :: (Total a, Fractional a) => Conn k (a, a) a
latticeN5 = Conn (uncurry joinN5) fork (uncurry meetN5)
  where
    joinN5 x y = maybe (1 / 0) (bool y x . (>= EQ)) (pcompare x y)

    meetN5 x y = maybe (-1 / 0) (bool y x . (<= EQ)) (pcompare x y)

extremalN5 :: (Total a, Fractional a) => Conn k () a
extremalN5 = Conn (const $ -1 / 0) (const ()) (const $ 1 / 0)

latticeOrd :: (Total a) => Conn k (a, a) a
latticeOrd = Conn (uncurry max) fork (uncurry min)

maybeL :: Triple () b => Conn k (Maybe a) (Either a b)
maybeL = Conn f g h
  where
    f = maybe (Right minimal) Left
    g = either Just (const Nothing)
    h = maybe (Right maximal) Left

maybeR :: Triple () a => Conn k (Maybe b) (Either a b)
maybeR = Conn f g h
  where
    f = maybe (Left minimal) Right
    g = either (const Nothing) Just
    h = maybe (Left maximal) Right

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
joinExtended Top          _            = Top
joinExtended _            Top          = Top
joinExtended (Extended x) (Extended y) = Extended (x `join` y)
joinExtended Bottom       y            = y
joinExtended x            Bottom       = x

meetExtended :: Right (a, a) a => Extended a -> Extended a -> Extended a
meetExtended Top          y            = y
meetExtended x            Top          = x
meetExtended (Extended x) (Extended y) = Extended (x `meet` y)
meetExtended Bottom       _            = Bottom
meetExtended _            Bottom       = Bottom

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
