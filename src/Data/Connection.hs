{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}

module Data.Connection (
  -- * Connections
    Connection(..)
  , ConnInteger
  , ConnNatural
  , lower
  , upper
  , fromInteger
  , fromNatural
  -- * Triples
  , Triple(..)
  , TripInteger
  , TripNatural
  , lower'
  , upper'
  , floor
  , ceiling
) where

import safe Data.Connection.Conn
import safe Data.Connection.Trip
import safe Data.Connection.Int
import safe Data.Connection.Word
import safe Data.Connection.Float
import safe Data.Connection.Ratio
import safe Data.Prd
import safe Data.Prd.Nan
import safe Data.Prd.Top
import safe Data.Word
import safe Data.Int
import safe Numeric.Natural
import safe Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))

import safe qualified Control.Category as C
import safe qualified Data.Set as Set
import safe qualified Data.IntSet as IntSet

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection

---------------------------------------------------------------------
-- Connection
---------------------------------------------------------------------

type ConnInteger a = Connection a (Maybe Integer)

type ConnNatural a = Connection a Natural

-- | A Galois connection between two monotone functions.
--
-- A Galois connection between /f/ and /g/ (denoted \(f \dashv g \))
-- is an adjunction in the category of partially ordered sets.
--
-- Each side of a connection may be defined in terms of the other:
-- 
--  \( g(x) = \sup \{y \in E \mid f(y) \leq x \} \)
--
--  \( f(x) = \inf \{y \in E \mid g(y) \geq x \} \)
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/Galois+connection>.
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

-- | A monotone function from the integers to /a/.
--
-- This is a lawful replacement for the version in base.
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = connr connection . Just

-- | A monotone function from the natural numbers to /a/.
--
fromNatural :: ConnNatural a => Natural -> a
fromNatural = connr connection

---------------------------------------------------------------------
-- Triple
---------------------------------------------------------------------

type TripInteger a = Triple a (Bound Integer)

type TripNatural a = Triple a (Top Natural)

-- | An adjoint triple of Galois connections.
--
-- An adjoint triple is a chain of connections of length 2:
--
-- \(f \dashv g \dashv h \) 
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/adjoint+triple>.
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

-- | A monotonic floor function.
--
-- >>> floor @Rational @Float (0 :% 0)
-- NaN
-- >>> floor @Rational @Float (1 :% 0)
-- Infinity
-- >>> floor @Rational @Float (13 :% 10)
-- 1.3
--
floor :: Triple a b => a -> b
floor = floorOn triple

-- | A monotonic ceiling function.
--
-- >>> ceiling @Rational @Float (0 :% 0)
-- NaN
-- >>> ceiling @Rational @Float (1 :% 0)
-- Infinity
-- >>> ceiling @Rational @Float (13 :% 10)
-- 1.3000001
--
-- 'ceiling' can be used to build lawful replacements for the 'Prelude.ceiling':
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

---------------------------------------------------------------------
-- Connection instances
---------------------------------------------------------------------

{-
instance Connection Bool Ordering where
  connection = binord

instance Connection Ordering Bool where
  connection = ordbin

instance Connection Bool CBool where
  connection = binc08

instance Connection CBool Bool where
  connection = c08bin

instance Connection Word8 CUChar where
  connection = w08c08
-}
instance Connection Word8 (Maybe Integer) where
  connection = w08nat C.>>> natint

instance Connection Word8 Natural where
  connection = w08nat

--instance Connection Word16 CUShort where
--  connection = w16c16

instance Connection Word16 (Maybe Integer) where
  connection = w16nat C.>>> natint

instance Connection Word16 Natural where
  connection = w16nat

--instance Connection Word32 CUInt where
--  connection = w32c32

instance Connection Word32 (Maybe Integer) where
  connection = w32nat C.>>> natint

instance Connection Word32 Natural where
  connection = w32nat

--instance Connection Word64 CULong where
--  connection = w64c64

instance Connection Word64 (Maybe Integer) where
  connection = w64nat C.>>> natint

instance Connection Word64 Natural where
  connection = w64nat

instance Connection Word (Maybe Integer) where
  connection = wxxnat C.>>> natint

instance Connection Word Natural where
  connection = wxxnat

instance Connection Natural (Maybe Integer) where
  connection = natint

instance Connection Int8 (Maybe Integer) where
  connection = i08int

instance Connection Int16 (Maybe Integer) where
  connection = i16int

instance Connection Int32 (Maybe Integer) where
  connection = i32int

instance Connection Int64 (Maybe Integer) where
  connection = i64int

instance Connection Int (Maybe Integer) where
  connection = ixxint

instance Connection Integer Natural where
  connection = intnat

{-
--instance Connection Float CFloat where
--  connection = f32c32

instance Connection (Nan Int32) Float where
  connection = i32f32

instance Connection Float (Nan Int32) where
  connection = f32i32

--instance Connection Float (Nan Int64) where
--  connection = f32i32 C.>>> mapped i32i64

--instance Connection Double CDouble where
--  connection = f64c64

instance Connection (Nan Int64) Double where
  connection = i64f64

instance Connection Double (Nan Int64) where
  connection = f64i64

instance Connection (Nan Int) Double where
  connection = ixxf64

instance Connection Double (Nan Int) where
  connection = f64ixx
-}
instance Prd a => Connection a a where
  connection = C.id

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
  connection = mapped connection

instance (Connection a b) => Connection (Extended a) (Extended b) where
  connection = mapped . mapped $ connection

mapped :: Functor f => Conn a b -> Conn (f a) (f b)
mapped (Conn f g) = Conn (fmap f) (fmap g)

---------------------------------------------------------------------
-- Triple instances
---------------------------------------------------------------------

instance Bounded a => Triple () a where
  triple = Trip (const minimal) (const ()) (const maximal)

instance Triple Int8 (Bound Integer) where
  triple = i08int'

instance Triple Int16 (Bound Integer) where
  triple = i16int'

instance Triple Int32 (Bound Integer) where
  triple = i32int'

instance Triple Int64 (Bound Integer) where
  triple = i64int'

instance Triple Int (Bound Integer) where
  triple = ixxint'

instance Triple Word8 (Top Natural) where
  triple = w08nat'

instance Triple Word16 (Top Natural) where
  triple = w16nat'

instance Triple Word32 (Top Natural) where
  triple = w32nat'

instance Triple Word64 (Top Natural) where
  triple = w64nat'

instance Triple Word (Top Natural) where
  triple = wxxnat'

instance Triple (Ratio Integer) (Nan Ordering) where
  triple = ratord

instance Triple (Ratio Integer) Float where
  triple = ratf32

instance Triple (Ratio Integer) Double where
  triple = ratf64

instance Triple (Ratio Integer) (Extended Int8) where
  triple = rati08

instance Triple (Ratio Integer) (Extended Int16) where
  triple = rati16

instance Triple (Ratio Integer) (Extended Int32) where
  triple = rati32

instance Triple (Ratio Integer) (Extended Int64) where
  triple = rati64

instance Triple (Ratio Integer) (Extended Integer) where
  triple = ratint

instance Triple (Ratio Natural) (Lifted Word8) where
  triple = ratw08

instance Triple (Ratio Natural) (Lifted Word16) where
  triple = ratw16

instance Triple (Ratio Natural) (Lifted Word32) where
  triple = ratw32

instance Triple (Ratio Natural) (Lifted Word64) where
  triple = ratw64

instance Triple (Ratio Natural) (Lifted Natural) where
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

instance Triple (IntSet.IntSet, IntSet.IntSet) IntSet.IntSet where
  triple = Trip (uncurry IntSet.union) (\x -> (x,x)) (uncurry IntSet.intersection)

instance Ord a => Triple (Set.Set a, Set.Set a) (Set.Set a) where
  triple = Trip (uncurry Set.union) (\x -> (x,x)) (uncurry Set.intersection)

instance Prd a => Triple a a where
  triple = C.id

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
