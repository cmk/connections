{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language DataKinds           #-}
{-# Language Safe                #-}
{-# Language ViewPatterns        #-}
{-# Language PatternSynonyms     #-}
{-# Language RankNTypes          #-}
{-# Language QuantifiedConstraints #-}

module Data.Connection.Class (
  -- * Types
    Kan(..)
  , Conn()
  , (\|/)
  , (/|\)
  -- * Connection L
  , ConnL
  , pattern ConnL
  , connL
  , swapL
  , embedL
  , ceiling
  , ceiling1
  , ceiling2
  -- * Connection R
  , ConnR
  , pattern ConnR
  , connR
  , swapR
  , floor
  , floor1
  , floor2
  , embedR
  -- * Connection
  , Trip
  , pattern Conn
  , Triple
  -- * Class
  , ConnFloat
  , ConnDouble
  , ConnInteger
  , ConnRational
  , ConnExtended
  , Connection(..)
) where

import safe Control.Category ((>>>))
import safe Data.Connection.Conn
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
import safe Data.Word
import safe Data.Int
import safe Numeric.Natural
import safe Prelude hiding (Bounded, floor, ceiling, fromInteger, fromRational)
import safe qualified Control.Category as C

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection


{-
-- >>> embed_ @Double @Int8 42
-- 42.0
embed_ :: (ConnExtended k a b, Bounded b) => b -> a
embed_ = embedL . Extended

ceiling_ :: (ConnExtended k a b, Bounded b) => a -> b
ceiling_ = retract . ceiling

floor_ :: (ConnExtended a b, Bounded b) => a -> b
floor_ = retract . floor

round_ :: (ConnExtended a b, Bounded b) => a -> b
round_ = retract . floor

truncate_ :: (ConnExtended a b, Bounded b) => a -> b
truncate_ = retract . floor
-}

type ConnInteger k = Connection k (Maybe Integer)
type ConnFloat k = Connection k Float
type ConnDouble k = Connection k Double
type ConnRational k = Connection k Rational
type ConnExtended k a b = Connection k a (Extended b)
type Triple a b = (Connection 'L a b, Connection 'R a b)

-- | An < https://ncatlab.org/nlab/show/adjoint+string adjoint string > of Galois connections of length 2 or 3.
--
class (Preorder a, Preorder b) => Connection k a b where

    -- |
    --
    -- >>> range (conn @_ @Double @Float) pi
    -- (3.1415925,3.1415927)
    -- >>> range (conn @_ @Rational @Float) (1 :% 7)
    -- (0.14285713,0.14285715)
    -- >>> range (conn @_ @Rational @Float) (1 :% 8)
    -- (0.125,0.125)
    --
    conn :: Conn k a b

---------------------------------------------------------------------
-- Connection L
---------------------------------------------------------------------

-- | A specialization of /conn/ to left-side connections.
--
-- This is a convenience function provided primarily to avoid needing
-- to enable /DataKinds/.
--
connL :: Connection 'L a b => ConnL a b
connL = conn @'L

-- | Extract the center of a 'Trip' or upper half of a 'ConnL'.
--
embedL :: Connection 'L a b => b -> a
embedL = embed connL

-- | Extract the ceiling of a 'Trip' or lower half of a 'ConnL'.
--
-- > ceiling @a @a = id
--
-- >>> ceiling @Rational @Float (0 :% 0)
-- NaN
-- >>> ceiling @Rational @Float (1 :% 0)
-- Infinity
-- >>> ceiling @Rational @Float (13 :% 10)
-- 1.3000001
--
ceiling :: Connection 'L a b => a -> b
ceiling = lowerL connL

-- | Lift a unary function over a 'ConnL'.
--
ceiling1 :: Connection 'L a b => (a -> a) -> b -> b
ceiling1 = lowerL1 connL

-- | Lift a binary function over a 'ConnL'.
--
ceiling2 :: Connection 'L a b => (a -> a -> a) -> b -> b -> b
ceiling2 = lowerL2 connL

---------------------------------------------------------------------
-- Connection R
---------------------------------------------------------------------

-- | A specialization of /conn/ to right-side connections.
--
-- This is a convenience function provided primarily to avoid needing
-- to enable /DataKinds/.
--
connR :: Connection 'R a b => ConnR a b
connR = conn @'R

-- | Extract the floor of a 'Trip' or upper half of a 'ConnL'.
--
-- > floor @a @a = id
--
-- >>> floor @Rational @Float (0 :% 0)
-- NaN
-- >>> floor @Rational @Float (1 :% 0)
-- Infinity
-- >>> floor @Rational @Float (13 :% 10)
-- 1.3
--
-- In conjunction with RebindableSyntax:
--
-- >>> fromInteger = floor . Right @()
-- >>> fromInteger @Int8 20000
-- 127
--
floor :: Connection 'R a b => a -> b
floor = upperR connR

-- | Lift a unary function over a 'ConnR'.
--
floor1 :: Connection 'R a b => (a -> a) -> b -> b
floor1 = upperR1 connR

-- | Lift a binary function over a 'ConnR'.
--
floor2 :: Connection 'R a b => (a -> a -> a) -> b -> b -> b
floor2 = upperR2 connR

-- | Extract the center of a 'Trip' or lower half of a 'ConnR'.
--
embedR :: Connection 'R a b => b -> a
embedR = embed connR

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Preorder a => Connection k a a where
  conn = C.id

instance Connection 'R Word16 Word8 where
  conn = swapR w08w16

instance Connection 'R Word32 Word8 where
  conn = swapR w08w32

instance Connection 'R Word32 Word16 where
  conn = swapR w16w32

instance Connection 'R Word64 Word8 where
  conn = swapR w08w64

instance Connection 'R Word64 Word16 where
  conn = swapR w16w64

instance Connection 'R Word64 Word32 where
  conn = swapR w32w64

instance Connection k Word Word64 where
  conn = wxxw64

instance Connection 'R Natural Word8 where
  conn = swapR w08nat

instance Connection 'R Natural Word16 where
  conn = swapR w16nat

instance Connection 'R Natural Word32 where
  conn = swapR w32nat

instance Connection 'R Natural Word64 where
  conn = swapR w64nat

instance Connection 'R Natural Word where
  conn = swapR wxxnat

instance Connection 'R Natural Integer where
  conn = swapR intnat

instance Connection 'R Int32 Int8 where
  conn = swapR i08i32

instance Connection 'R Int32 Int16 where
  conn = swapR i16i32

instance Connection 'R Int64 Int8 where
  conn = swapR i08i64

instance Connection 'R Int64 Int16 where
  conn = swapR i16i64

instance Connection 'R Int64 Int32 where
  conn = swapR i32i64

instance Connection k Int Int64 where
  conn = ixxi64

instance Connection 'R (Maybe Integer) Word8 where
  conn = swapR $ w08nat >>> natint

instance Connection 'R (Maybe Integer) Word16 where
  conn = swapR $ w16nat >>> natint

instance Connection 'R (Maybe Integer) Word32 where
  conn = swapR $ w32nat >>> natint

instance Connection 'R (Maybe Integer) Word64 where
  conn = swapR $ w64nat >>> natint

instance Connection 'R (Maybe Integer) Word where
  conn = swapR $ wxxnat >>> natint

instance Connection 'R (Maybe Integer) Natural where
  conn = swapR natint

instance Connection 'R (Maybe Integer) Int8 where
  conn = swapR i08int

instance Connection 'R (Maybe Integer) Int16 where
  conn = swapR i16int

instance Connection 'R (Maybe Integer) Int32 where
  conn = swapR i32int

instance Connection 'R (Maybe Integer) Int64 where
  conn = swapR i64int

instance Connection 'R (Maybe Integer) Int where
  conn = swapR ixxint

instance Connection 'R (Maybe Integer) Integer where
  -- | Provided as a shim for /RebindableSyntax/.
  -- Note that this instance will clip negative numbers to zero.
  conn = swapR $ intnat >>> natint

instance Connection k Int8 Word8 where
  conn = i08w08

instance Connection k Int16 Word16 where
  conn = i16w16

instance Connection k Int32 Word32 where
  conn = i32w32

instance Connection k Int64 Word64 where
  conn = i64w64

instance Connection k Int Word where
  conn = ixxwxx

instance Connection k Double Float where
  conn = f64f32

instance Connection k Rational Float where
  conn = ratf32

instance Connection k Rational Double where
  conn = ratf64

instance Connection k Rational (Extended Int8) where
  conn = rati08

instance Connection k Rational (Extended Int16) where
  conn = rati16

instance Connection k Rational (Extended Int32) where
  conn = rati32

instance Connection k Rational (Extended Int64) where
  conn = rati64

instance Connection k Rational (Extended Int) where
  conn = ratixx

instance Connection k Rational (Extended Integer) where
  conn = ratint

instance Connection k Float (Extended Int8) where
  conn = f32i08

instance Connection k Float (Extended Int16) where
  conn = f32i16

instance Connection 'L Float (Extended Int32) where
  conn = conn >>> fmapped (i16w16 >>> w16w32 >>> w32i32)

instance Connection 'L Float (Extended Int64) where
  conn = conn >>> fmapped (i16w16 >>> w16w64 >>> w64i64)

instance Connection 'L Float (Extended Int) where
  conn = conn >>> fmapped (i16w16 >>> w16wxx >>> swapL ixxwxx)

instance Connection k Double (Extended Int8) where
  conn = f64i08

instance Connection k Double (Extended Int16) where
  conn = f64i16

instance Connection k Double (Extended Int32) where
  conn = f64i32

instance Connection 'L Double (Extended Int64) where
  conn = conn >>> fmapped (i32w32 >>> w32w64 >>> w64i64)

instance Connection 'L Double (Extended Int) where
  conn = conn >>> fmapped (i32w32 >>> w32wxx >>> swapL ixxwxx)

instance Connection k a b => Connection k (Identity a) b where
  conn = Conn runIdentity Identity runIdentity >>> conn

instance Connection k a b => Connection k a (Identity b) where
  conn = conn >>> Conn Identity runIdentity Identity

instance (Connection k a b, Connection k c d) => Connection k (Either a c) (Either b d) where
  -- |
  -- > conn :: Connection k a b => Connection k (Lifted a) (Lifted b) 
  -- > conn :: Connection k a b => Connection k (Lowered a) (Lowered b) 
  conn = choice conn conn

instance Connection k a b => Connection k (Maybe a) (Maybe b) where
  conn = fmapped conn

instance Connection k a b => Connection k (Extended a) (Extended b) where
  conn = fmapped conn

instance Connection k a b => Connection k [a] [b] where
  conn = fmapped conn

instance (Connection k a b, Connection k c d) => Connection k (a, c) (b, d) where
  conn = strong conn conn

instance (Connection k a b, Foldable1 f, Representable f, Lattice a) => Connection k (Co f a) b where
  conn = Conn unCo Co unCo >>> Conn join1 pureRep meet1 >>> conn
