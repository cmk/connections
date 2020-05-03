{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}

module Data.Connection (
  -- * Connections
    ConnInteger
  , Connection(..)
  , lower
  , upper
  , fromInteger
  -- * Triples 
  , TripFloat
  , TripDouble
  , TripRational
  , TripPositive
  , Triple(..)
  , lower'
  , upper'
  , round
  , floor
  , ceiling
  , truncate
  , fromRational
) where

import Control.Category ((>>>))
import Data.Bool
import Data.Connection.Conn
import Data.Connection.Trip
import Data.Connection.Int
import Data.Connection.Float
import Data.Connection.Ratio
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Top
import Data.Word
import Data.Int
import Numeric.Natural
import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))

import qualified Control.Category as C

---------------------------------------------------------------------
-- Connection
---------------------------------------------------------------------

type ConnInteger a = Connection (Bound Integer) a

-- | A Galois connection between two monotone functions.
--
-- See <https://ncatlab.org/nlab/show/Galois+connection>
--
class (Prd a, Prd b) => Connection a b where
  connection :: Conn a b

-- | The lower half of a Galois connection.
--
lower :: Connection a b => a -> b
lower = connl connection

-- | The upper half of a Galois connection.
--
upper :: Connection a b => b -> a
upper = connr connection

-- | A lawful replacement for the version in base.
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = connl connection . Just . Fin

---------------------------------------------------------------------
-- Triple
---------------------------------------------------------------------

type TripRational a = Triple Rational a

type TripPositive a = Triple Positive a

type TripFloat a = Triple Float (Extended a)

type TripDouble a = Triple Double (Extended a)

-- | An adjoint triple of Galois connections.
--
-- @'Trip' f g h@ satisfies:
--
-- @
-- f ⊣ g
-- ⊥   ⊥
-- g ⊣ h
-- @
--
-- See <https://ncatlab.org/nlab/show/adjoint+triple>
--
class (Prd a, Prd b) => Triple a b where
  triple :: Trip a b

-- | The lower half of a Galois triple.
--
lower' :: Triple a b => Conn a b
lower' = tripl triple

-- | The upper half of a Galois triple.
--
upper' :: Triple a b => Conn b a
upper' = tripr triple

-- | A lawful round-to-nearest function.
--
-- >>> round32 = mapNan (bounded id) . Data.Connection.round @Float
-- >>> round32 5.3 :: Nan Int8
-- Def 5
-- >>> P.round @Float @Int8 $ 0/0
-- 0
-- >>> round32 @Float @Int8 $ 0/0
-- Nan
-- >>> P.round @Float @Int8 $ 1/0
-- 0
-- >>> round32 @Int8 $ 1/0
-- Def 127
-- >>> P.round @Float @Int8 129
-- -127
-- >>> round32 @Int8 129
-- Def 127
-- >>> P.round @Float @Int8 $ -129
-- 127
-- >>> round32 @Int8 $ -129
-- Def (-128)
-- >>> P.round @Float @Int8 $ -130
-- 126
-- >>> round32 @Int8 $ -130
-- Def (-128)
-- 
round :: (Num a, Triple a b) => a -> b
round = roundOn triple

-- | A lawful monotonic floor function.
--
floor :: Triple a b => a -> b
floor = floorOn triple

-- | A lawful monotonic ceiling function.
--
-- >>> ceiling32 = mapNan (bounded id) . ceiling @Float
-- >>> P.ceiling @Float @Int8 129
-- -127
-- >>> ceiling32 @Int8 129
-- Def 127
-- >>> P.ceiling @Float @Int8 (0/0)
-- 0
-- >>> ceiling32 @Int8 (0/0)
-- Nan
--
ceiling :: Triple a b => a -> b
ceiling = ceilingOn triple

-- | A lawful round-towards-zero function.
--
-- >>> truncate32 = mapNan (bounded id) . truncate @Float
-- >>> truncate32 @Int16 5.4
-- Def 5
-- >>> truncate32 @Int16 (-5.4)
-- Def (-5)
--
truncate :: (Num a, Triple a b) => a -> b
truncate = truncateOn triple

-- | A lawful replacement for the version in base.
--
-- >>> fromRational @Float 1.3
-- 1.3000001
-- >>> fromRational @Float (1/0)
-- Infinity
-- >>> fromRational @Float (0/0)
-- NaN
--
fromRational :: TripRational a => Rational -> a
fromRational = ceiling

---------------------------------------------------------------------
-- Connection instances
---------------------------------------------------------------------

instance Prd a => Connection a a where
  connection = C.id

instance Connection Bool Ordering where
  connection = Conn f g where
    f False = LT
    f _     = EQ

    g LT = False
    g _  = True

instance Connection Ordering Bool where
  connection = Conn f g where
    f GT = True
    f _  = False

    g True = GT
    g _    = EQ

instance Connection (Bound Integer) Int8 where
  connection = tripr i08int

instance Connection (Bound Integer) Int16 where
  connection = tripr i16int

instance Connection (Bound Integer) Int32 where
  connection = tripr i32int

instance Connection (Bound Integer) Int64 where
  connection = tripr i64int

instance Connection (Bound Integer) Int where
  connection = tripr ixxint

instance Connection (Bound Integer) Word8 where
  connection = tripr i08int >>> i08w08

instance Connection (Bound Integer) Word16 where
  connection = tripr i16int >>> i16w16

instance Connection (Bound Integer) Word32 where
  connection = tripr i32int >>> i32w32

instance Connection (Bound Integer) Word64 where
  connection = tripr i64int >>> i64w64

instance Connection (Bound Integer) Word where
  connection = tripr ixxint >>> ixxwxx

instance Connection a b => Connection (Down b) (Down a) where
  connection = dual connection

instance (Connection a b, Connection c d) => Connection (a, c) (b, d) where
  connection = strong connection connection

instance (Connection a b, Prd c) => Connection (c, a) (c, b) where
  connection = strong C.id connection

instance (Connection a b, Prd c) => Connection (a, c) (b, c) where
  connection = flip strong C.id connection

instance (Connection a b, Connection c d) => Connection (Either a c) (Either b d) where
  connection = choice connection connection

instance (Connection a b, Prd c) => Connection (Either c a) (Either c b) where
  connection = choice C.id connection

instance (Connection a b, Prd c) => Connection (Either a c) (Either b c) where
  connection = flip choice C.id connection

instance (Connection a b) => Connection [a] [b] where
  connection = mapped connection

instance (Connection a b) => Connection (Maybe a) (Maybe b) where
  connection = mapped connection

instance (Connection a b) => Connection (Top a) (Top b) where
  connection = mapped connection

instance (Connection a b) => Connection (Nan a) (Nan b) where
  connection = mapped connection

instance (Connection a b) => Connection (Bound a) (Bound b) where
  connection = mapped . mapped $ connection

instance (Connection a b) => Connection (Extended a) (Extended b) where
  connection = mapped . mapped . mapped $ connection

mapped :: Functor f => Conn a b -> Conn (f a) (f b)
mapped (Conn f g) = Conn (fmap f) (fmap g)

---------------------------------------------------------------------
-- Triple instances
---------------------------------------------------------------------

instance Prd a => Triple a a where
  triple = C.id

instance Bounded a => Triple () a where
  triple = Trip (const minimal) (const ()) (const maximal)

instance Triple Rational (Nan Ordering) where
  triple = ratord

instance Triple Rational Float where
  triple = ratf32

instance Triple Rational Double where
  triple = ratf64

instance Triple Rational (Extended Int8) where
  triple = rati08

instance Triple Rational (Extended Int16) where
  triple = rati16

instance Triple Rational (Extended Int32) where
  triple = rati32

instance Triple Rational (Extended Int64) where
  triple = rati64

instance Triple Rational (Extended Integer) where
  triple = ratint

instance Triple Positive (Lifted Word8) where
  triple = ratw08

instance Triple Positive (Lifted Word16) where
  triple = ratw16

instance Triple Positive (Lifted Word32) where
  triple = ratw32

instance Triple Positive (Lifted Word64) where
  triple = ratw64

instance Triple Positive (Lifted Natural) where
  triple = ratnat

instance Triple Float (Extended Int8) where
  triple = f32i08

instance Triple Float (Extended Int16) where
  triple = f32i16

instance Triple Double (Extended Int8) where
  triple = f64i08

instance Triple Double (Extended Int16) where
  triple = f64i16

instance Triple Double (Extended Int32) where
  triple = f64i32

instance (Triple a b, Triple c d) => Triple (a, c) (b, d) where
  triple = strong' triple triple

instance (Triple a b, Prd c) => Triple (a, c) (b, c) where
  triple = flip strong' C.id triple

instance (Triple a b, Prd c) => Triple (c, a) (c, b) where
  triple = strong' C.id triple

instance (Triple a b, Triple c d) => Triple (Either a c) (Either b d) where
  triple = choice' triple triple

instance (Triple a b, Prd c) => Triple (Either c a) (Either c b) where
  triple = choice' C.id triple

instance (Triple a b, Prd c) => Triple (Either a c) (Either b c) where
  triple = flip choice' C.id triple

instance (Triple a b, Bounded b) => Triple (Maybe a) (Either a b) where
  triple = Trip f g h where
    f = maybe (Right minimal) Left
    g = either Just (const Nothing)
    h = maybe (Right maximal) Left

instance (Triple a b, Bounded a) => Triple (Maybe b) (Either a b) where
  triple = Trip f g h where
    f = maybe (Left minimal) Right
    g = either (const Nothing) Just
    h = maybe (Left maximal) Right

{-
instance (Triple a b) => Triple [a] [b] where
  triple = mapped' triple

instance (Triple a b) => Triple (Maybe a) (Maybe b) where
  triple = mapped' triple

instance (Triple a b) => Triple (Top a) (Top b) where
  triple = mapped' triple

instance (Triple a b) => Triple (Nan a) (Nan b) where
  triple = mapped' triple

instance (Triple a b) => Triple (Bound a) (Bound b) where
  triple = mapped' . mapped' $ triple

instance (Triple a b) => Triple (Extended a) (Extended b) where
  triple = mapped' . mapped' . mapped' $ triple

mapped' :: Functor f => Trip a b -> Trip (f a) (f b)
mapped' (Trip f g h) = Trip (fmap f) (fmap g) (fmap h)
-}
