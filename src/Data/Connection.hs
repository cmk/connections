{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}

module Data.Connection (
  -- * Connection
    Connection(..)
  , left
  , right
  -- * Triple
  , Triple(..)
  , embed
  , floor
  , ceiling
  -- * Conn
  , Conn(..)
  , connl
  , connr
  , connl1
  , connr1
  , connl2
  , connr2
  , unit
  , counit
  , (|||)
  , (&&&)
  -- * Trip
  , Trip(..)
  , tripl
  , tripr
  , unit'
  , counit'
  , joined
  , forked
) where

import safe Control.Applicative (liftA2)
import safe Data.Connection.Type
import safe Data.Connection.Int
import safe Data.Connection.Word
import safe Data.Connection.Float
import safe Data.Connection.Double
import safe Data.Connection.Ratio
import safe Data.Functor.Identity
import safe Data.Functor.Rep 
import safe Data.Semigroup.Join
import safe Data.Semigroup.Foldable
import safe Data.Lattice
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Interval
import safe Data.Word
import safe Data.Int
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Bounded, fromInteger, fromRational, RealFrac(..))
import safe qualified Control.Category as C

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection

---------------------------------------------------------------------
-- Connection
---------------------------------------------------------------------

-- | A < https://ncatlab.org/nlab/show/Galois+connection connection > between two monotone functions.
--
-- A Galois connection between /f/ and /g/ (often denoted \(f \dashv g \))
-- is an adjunction in the category of partially ordered sets.
--
-- Each side of a connection may be defined in terms of the other:
-- 
--  \( g(x) = \sup \{y \in E \mid f(y) \leq x \} \)
--
--  \( f(x) = \inf \{y \in E \mid g(y) \geq x \} \)
--
-- For further information see 'Data.Connection.Property'.
--
class (Preorder a, Preorder b) => Connection a b where

    connection :: Conn a b

-- | The left half of a Galois connection.
--
left :: Connection a b => a -> b
left = connl connection

-- | The right half of a Galois connection.
--
right :: Connection a b => b -> a
right = connr connection

---------------------------------------------------------------------
-- Triple
---------------------------------------------------------------------

-- | An < https://ncatlab.org/nlab/show/adjoint+triple adjoint triple > of Galois connections.
--
-- An adjoint triple is a chain of connections of length 2:
--
-- \(f \dashv g \dashv h \) 
--
-- For further information see 'Data.Connection.Property'.
--
class (Preorder a, Preorder b) => Triple a b where

    triple :: Trip a b

-- | Embed a value into a more refined order.
--
embed :: Triple a b => b -> a
embed = connl . tripr $ triple

-- | A monotonic floor function.
--
-- > floor @a @a = id
--
-- >>> floor @Rational @Float (0 :% 0)
-- NaN
-- >>> floor @Rational @Float (1 :% 0)
-- Infinity
-- >>> floor @Rational @Float (13 :% 10)
-- 1.3
-- >>> floor @(Interval Int) @Int (1 ... 2)
-- 1
-- >>> floor @(Interval Int) @Int (-2 ... -1)
-- -2
--
floor :: Triple a b => a -> b
floor = connr . tripr $ triple 

-- | A monotonic ceiling function.
--
-- > ceiling @a @a = id
--
-- >>> ceiling @Rational @Float (0 :% 0)
-- NaN
-- >>> ceiling @Rational @Float (1 :% 0)
-- Infinity
-- >>> ceiling @Rational @Float (13 :% 10)
-- 1.3000001
-- >>> ceiling @(Interval Int) @Int (1 ... 2)
-- 2
-- >>> ceiling @(Interval Int) @Int (-2 ... -1)
-- -1
--
ceiling :: Triple a b => a -> b
ceiling = connl . tripl $ triple

---------------------------------------------------------------------
-- Connection instances
---------------------------------------------------------------------

instance Preorder a => Connection a a where
  connection = C.id

instance LowerBounded a => Connection () a where
  connection = Conn (const bottom) (const ())

instance UpperBounded a => Connection a () where
  connection = Conn (const ()) (const top)

instance Connection Word8 (Lifted Integer) where
  connection = w08nat C.>>> natint

instance Connection Word8 Natural where
  connection = w08nat

instance Connection Word16 (Lifted Integer) where
  connection = w16nat C.>>> natint

instance Connection Word16 Natural where
  connection = w16nat

instance Connection Word32 (Lifted Integer) where
  connection = w32nat C.>>> natint

instance Connection Word32 Natural where
  connection = w32nat

instance Connection Word64 (Lifted Integer) where
  connection = w64nat C.>>> natint

instance Connection Word64 Natural where
  connection = w64nat

instance Connection Word (Lifted Integer) where
  connection = wxxnat C.>>> natint

instance Connection Word Natural where
  connection = wxxnat

instance Connection Natural (Lifted Integer) where
  connection = natint

instance Connection Int8 (Lifted Integer) where
  connection = i08int

instance Connection Int16 (Lifted Integer) where
  connection = i16int

instance Connection Int32 (Lifted Integer) where
  connection = i32int

instance Connection Int64 (Lifted Integer) where
  connection = i64int

instance Connection Int (Lifted Integer) where
  connection = ixxint

instance Connection Integer Natural where
  connection = intnat

instance Connection Integer (Lifted Integer) where
  connection = intnat C.>>> natint

instance Connection a b => Connection (Identity a) b where
  connection = Conn runIdentity Identity C.>>> connection

instance Connection a b => Connection a (Identity b) where
  connection = connection C.>>> Conn Identity runIdentity

instance Connection a b => Connection (Down b) (Down a) where
  connection = dual connection

instance (Connection a b, Connection c d) => Connection (Either a c) (Either b d) where
  -- |
  -- > connection :: Connection a b => Connection (Lifted a) (Lifted b) 
  -- > connection :: Connection a b => Connection (Lowered a) (Lowered b) 
  connection = choice connection connection

instance Connection a b => Connection (Maybe a) (Maybe b) where
  connection = mapped connection

instance Connection a b => Connection (Extended a) (Extended b) where
  connection = mapped connection

instance Connection a b => Connection [a] [b] where
  connection = mapped connection

instance (Connection a b, Connection c d) => Connection (a, c) (b, d) where
  connection = strong connection connection

---------------------------------------------------------------------
-- Triple instances
---------------------------------------------------------------------

instance Preorder a => Triple a a where
  triple = C.id

instance Bounded a => Triple () a where
  triple = Trip (const top) (const ()) (const bottom)

instance Triple Double Float where
  triple = f64f32

instance Triple Rational Float where
  triple = ratf32

instance Triple Rational Double where
  triple = ratf64

instance Triple Positive (Lowered Word8) where
  triple = ratw08

instance Triple Positive (Lowered Word16) where
  triple = ratw16

instance Triple Positive (Lowered Word32) where
  triple = ratw32

instance Triple Positive (Lowered Word64) where
  triple = ratw64

instance Triple Positive (Lowered Natural) where
  triple = ratnat

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

instance Triple a b => Triple (Identity a) b where
  triple = Trip runIdentity Identity runIdentity C.>>> triple

instance Triple a b => Triple a (Identity b) where
  triple = triple C.>>> Trip Identity runIdentity Identity

instance (Triple a b, Triple c d) => Triple (Either a c) (Either b d) where
  -- |
  -- > triple :: Triple a b => Triple (Lifted a) (Lifted b) 
  -- > triple :: Triple a b => Triple (Lowered a) (Lowered b) 
  triple = choice' triple triple

instance Triple a b => Triple (Maybe a) (Maybe b) where
  triple = mapped' triple

instance Triple a b => Triple (Extended a) (Extended b) where
  triple = mapped' triple

instance Triple a b => Triple [a] [b] where
  triple = mapped' triple

instance (Triple a b, Triple c d) => Triple (a, c) (b, d) where
  triple = strong' triple triple

--instance LowerBounded a => Triple (Maybe a) (Interval a) where
--  triple = interval

instance (Triple a b, Foldable1 f, Representable f, Lattice a) => Triple (Co f a) b where
  triple = Trip unCo Co unCo C.>>> Trip join1 pureRep meet1 C.>>> triple
