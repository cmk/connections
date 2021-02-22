{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Connection.Class (
    -- * Types
    Conn (),
    identity,
    choice,
    strong,
    (/|\),
    (\|/),

    -- * Connection k
    Triple,
    ConnK,
    pattern Conn,
    half,
    midpoint,
    round,
    round1,
    round2,
    truncate,
    truncate1,
    truncate2,
    extremal,
    lub,
    glb,

    -- * Connection L
    Left,
    ConnL,
    pattern ConnL,
    connL,
    embedL,
    minimal,
    join,
    ceiling,
    ceiling1,
    ceiling2,

    -- * Connection R
    Right,
    ConnR,
    pattern ConnR,
    connR,
    embedR,
    maximal,
    meet,
    floor,
    floor1,
    floor2,

    -- * Connection
    Kan (..),
    ConnInteger,
    ConnRational,
    ConnExtended,
    Connection (..),
) where

import safe Control.Category ((>>>))
import safe Data.Bool (bool)
import safe Data.Connection.Conn
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

type Right = Connection 'R

-- | A constraint kind representing an <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
type Triple a b = (Left a b, Right a b)

-- | A constraint kind for 'Integer' conversions.
--
--  Usable in conjunction with /RebindableSyntax/:
--
--  > fromInteger = embedL . Just :: ConnInteger a => Integer -> a
type ConnInteger a = Left a (Maybe Integer)

-- | A constraint kind for 'Rational' conversions.
--
-- Usable in conjunction with /RebindableSyntax/:
--
--  > fromRational = round :: ConnRational a => Rational -> a
type ConnRational a = Triple Rational a

type ConnExtended a b = Triple a (Extended b)

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
class (Preorder a, Preorder b) => Connection k a b where
    -- |
    --
    -- >>> range (conn @_ @Rational @Float) (22 :% 7)
    -- (3.142857,3.1428573)
    -- >>> range (conn @_ @Double @Float) pi
    -- (3.1415925,3.1415927)
    conn :: Conn k a b

infixr 3 \|/

-- | A preorder variant of 'Control.Arrow.|||'.
(\|/) :: Conn k c a -> Conn k c b -> Conn k c (Either a b)
f \|/ g = Conn Left (either id id) Right >>> f `choice` g

infixr 4 /|\

-- | A preorder variant of 'Control.Arrow.&&&'.
(/|\) :: Connection k (c, c) c => Conn k a c -> Conn k b c -> Conn k (a, b) c
f /|\ g = f `strong` g >>> conn

---------------------------------------------------------------------
-- Connection k
---------------------------------------------------------------------

-- | Return the nearest value to x.
--
-- > round @a @a = id
--
-- If x lies halfway between two finite values, then return the value
-- with the larger absolute value (i.e. round away from zero).
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
round :: forall a b. (Num a, Triple a b) => a -> b
round x = case pcompare halfR halfL of
    Just GT -> ceiling x
    Just LT -> floor x
    _ -> truncate x
  where
    halfR = x - lower (connR @a @b) x -- dist from lower bound
    halfL = upper (connL @a @b) x - x -- dist from upper bound

-- | Lift a unary function over a 'Conn'.
--
-- Results are rounded to the nearest value with ties away from 0.
round1 :: (Num a, Triple a b) => (a -> a) -> b -> b
round1 f x = round $ f (g x) where Conn _ g _ = connL
{-# INLINE round1 #-}

-- | Lift a binary function over a 'Conn'.
--
-- Results are rounded to the nearest value with ties away from 0.
--
-- Example avoiding loss of precision:
-- >>> f x y = (x + y) - x
-- >>> maxOdd32 = 1.6777215e7
-- >>> maxOdd64 = 9.007199254740991e15
-- >>> f maxOdd32 2.0 :: Float
-- 1.0
-- >>> round2 @Rational @Float f maxOdd32 2.0
-- 2.0
-- >>> f maxOdd64 2.0 :: Double
-- 1.0
-- >>> round2 @Rational @Double f maxOdd64 2.0
-- 2.0
round2 :: (Num a, Triple a b) => (a -> a -> a) -> b -> b -> b
round2 f x y = round $ f (g x) (g y) where Conn _ g _ = connL
{-# INLINE round2 #-}

-- | Truncate towards zero.
--
-- > truncate @a @a = id
truncate :: (Num a, Triple a b) => a -> b
truncate x = if x >~ 0 then floor x else ceiling x

-- | Lift a unary function over a 'Conn'.
--
-- Results are truncated towards 0.
truncate1 :: (Num a, Triple a b) => (a -> a) -> b -> b
truncate1 f x = truncate $ f (g x) where Conn _ g _ = connL
{-# INLINE truncate1 #-}

-- | Lift a binary function over a 'Conn'.
--
-- Results are truncated towards 0.
truncate2 :: (Num a, Triple a b) => (a -> a -> a) -> b -> b -> b
truncate2 f x y = truncate $ f (g x) (g y) where Conn _ g _ = connL
{-# INLINE truncate2 #-}

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

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
lub :: Triple (a, a) a => a -> a -> a -> a
lub x y z = (x `meet` y) `join` (y `meet` z) `join` (z `meet` x)

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
glb x y z = (x `join` y) `meet` (y `join` z) `meet` (z `join` x)

---------------------------------------------------------------------
-- Connection L
---------------------------------------------------------------------

-- | A specialization of /conn/ to left-side connections.
--
-- This is a convenience function provided primarily to avoid needing
-- to enable /DataKinds/.
connL :: Left a b => ConnL a b
connL = conn @ 'L

-- | Extract the center of a 'Conn' or upper half of a 'ConnL'.
embedL :: Left a b => b -> a
embedL = embed connL

-- | A minimal element of a preorder.
--
-- 'minimal' needn't be unique, but it must obey:
--
-- > x <~ minimal => x ~~ minimal
minimal :: Left () a => a
minimal = ceiling ()

infixr 5 `join`

-- | Semigroup operation on a join-lattice.
join :: Left (a, a) a => a -> a -> a
join = curry ceiling

-- | Extract the ceiling of a 'Conn' or lower half of a 'ConnL'.
--
-- > ceiling @a @a = id
-- > ceiling (x1 `join` a2) = ceiling x1 `join` ceiling x2
--
-- The latter law is the adjoint functor theorem for preorders.
--
-- >>> Data.Connection.ceiling @Rational @Float (0 :% 0)
-- NaN
-- >>> Data.Connection.ceiling @Rational @Float (1 :% 0)
-- Infinity
-- >>> Data.Connection.ceiling @Rational @Float (13 :% 10)
-- 1.3000001
ceiling :: Left a b => a -> b
ceiling = ceilingWith conn

-- | Lift a unary function over a 'ConnL'.
ceiling1 :: Left a b => (a -> a) -> b -> b
ceiling1 = ceilingWith1 conn

-- | Lift a binary function over a 'ConnL'.
ceiling2 :: Left a b => (a -> a -> a) -> b -> b -> b
ceiling2 = ceilingWith2 conn

---------------------------------------------------------------------
-- Connection R
---------------------------------------------------------------------

-- | A specialization of /conn/ to right-side connections.
--
-- This is a convenience function provided primarily to avoid needing
-- to enable /DataKinds/.
connR :: Right a b => ConnR a b
connR = conn @ 'R

-- | Extract the center of a 'ConnK' or lower half of a 'ConnR'.
embedR :: Right a b => b -> a
embedR = embed connR

-- | A maximal element of a preorder.
--
-- 'maximal' needn't be unique, but it must obey:
--
-- > x >~ maximal => x ~~ maximal
maximal :: Right () a => a
maximal = floor ()

infixr 6 `meet`

-- | Semigroup operation on a meet-lattice.
meet :: Right (a, a) a => a -> a -> a
meet = curry floor

-- | Extract the floor of a 'ConnK' or upper half of a 'ConnL'.
--
-- > floor @a @a = id
-- > floor (x1 `meet` x2) = floor x1 `meet` floor x2
--
-- The latter law is the adjoint functor theorem for preorders.
--
-- >>> Data.Connection.floor @Rational @Float (0 :% 0)
-- NaN
-- >>> Data.Connection.floor @Rational @Float (1 :% 0)
-- Infinity
-- >>> Data.Connection.floor @Rational @Float (13 :% 10)
-- 1.3
floor :: Right a b => a -> b
floor = floorWith conn

-- | Lift a unary function over a 'ConnR'.
floor1 :: Right a b => (a -> a) -> b -> b
floor1 = floorWith1 conn

-- | Lift a binary function over a 'ConnR'.
floor2 :: Right a b => (a -> a -> a) -> b -> b -> b
floor2 = floorWith2 conn

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

{-
instance Connection 'L Integer (Maybe Integer) where
  -- | Provided as a shim for /RebindableSyntax/.
  -- Note that this instance will clip negative numbers to zero.
conn = swapR $ intnat >>> natint
-}

instance Connection k Rational (Extended Int8) where conn = rati08
instance Connection k Rational (Extended Int16) where conn = rati16
instance Connection k Rational (Extended Int32) where conn = rati32
instance Connection k Rational (Extended Int64) where conn = rati64
instance Connection k Rational (Extended Int) where conn = ratixx
instance Connection k Rational (Extended Integer) where conn = ratint

-- | All 'Data.Int.Int08' values are exactly representable in a 'Float'.
instance Connection k Float (Extended Int8) where conn = f32i08

-- | All 'Data.Int.Int16' values are exactly representable in a 'Float'.
instance Connection k Float (Extended Int16) where conn = f32i16

-- | All 'Data.Int.Int08' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int8) where conn = f64i08

-- | All 'Data.Int.Int16' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int16) where conn = f64i16

-- | All 'Data.Int.Int32' values are exactly representable in a 'Double'.
instance Connection k Double (Extended Int32) where conn = f64i32

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
    conn = set

instance Connection 'L () IntSet.IntSet where
    conn = ConnL (const IntSet.empty) (const ())

instance Connection k (IntSet.IntSet, IntSet.IntSet) IntSet.IntSet where
    conn = intSet

instance (Total a, Preorder b) => Connection 'L () (Map.Map a b) where
    conn = ConnL (const Map.empty) (const ())

instance (Total a, Left (b, b) b) => Connection 'L (Map.Map a b, Map.Map a b) (Map.Map a b) where
    conn = ConnL (uncurry $ Map.unionWith join) fork

instance (Total a, Right (b, b) b) => Connection 'R (Map.Map a b, Map.Map a b) (Map.Map a b) where
    conn = ConnR fork (uncurry $ Map.intersectionWith meet)

instance Preorder a => Connection 'L () (IntMap.IntMap a) where
    conn = ConnL (const IntMap.empty) (const ())

instance Left (a, a) a => Connection 'L (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    conn = ConnL (uncurry $ IntMap.unionWith join) fork

instance Right (a, a) a => Connection 'R (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    conn = ConnR fork (uncurry $ IntMap.intersectionWith meet)

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

meetMaybe :: Connection 'R (a, a) a => Maybe a -> Maybe a -> Maybe a
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

meetExtended :: Connection 'R (a, a) a => Extended a -> Extended a -> Extended a
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

meetEither :: (Connection 'R (a, a) a, Connection 'R (b, b) b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x `meet` y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x `meet` y)

joinTuple :: (Connection 'L (a, a) a, Connection 'L (b, b) b) => (a, b) -> (a, b) -> (a, b)
joinTuple (x1, y1) (x2, y2) = (x1 `join` x2, y1 `join` y2)

meetTuple :: (Connection 'R (a, a) a, Connection 'R (b, b) b) => (a, b) -> (a, b) -> (a, b)
meetTuple (x1, y1) (x2, y2) = (x1 `meet` x2, y1 `meet` y2)
-}
