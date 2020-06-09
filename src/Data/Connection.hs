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
  , left
  , right
  , fromInteger
  , fromNatural
  -- * Triples
  , Triple(..)
  , TripRatio
  --, TripInteger
  --, TripNatural
  , floor
  , ceiling
  -- * Yoneda representations
  , type Ideal
  , type Filter
  , lower
  , upper
) where

import safe Data.Connection.Type
import safe Data.Connection.Int
import safe Data.Connection.Word
import safe Data.Connection.Float
import safe Data.Connection.Ratio
import safe Data.Semigroup.Join
import safe Data.Lattice
import safe Data.Ord
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

type ConnInteger a = Connection a (Lifted Integer)

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
class Connection a b where

    connection :: Conn a b

-- | The left half of a Galois connection.
--
left :: Connection a b => a -> b
left = connl connection

-- | The right half of a Galois connection.
--
right :: Connection a b => b -> a
right = connr connection

-- | A monotone function from the integers to /a/.
--
-- This is a lawful replacement for the version in base.
--
fromInteger :: ConnInteger a => Integer -> a
fromInteger = right . Right @()

-- | A monotone function from the natural numbers to /a/.
--
fromNatural :: ConnNatural a => Natural -> a
fromNatural = right

---------------------------------------------------------------------
-- Triple
---------------------------------------------------------------------

type TripRatio a b = Triple (Ratio a) b

--type TripInteger a = Triple a (Extended Integer)

--type TripNatural a = Triple a (Lowered Natural)

-- | An adjoint triple of Galois connections.
--
-- An adjoint triple is a chain of connections of length 2:
--
-- \(f \dashv g \dashv h \) 
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/adjoint+triple>.
--
class Triple a b where

    triple :: Trip a b

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
-- Ideals and filters
---------------------------------------------------------------------

-- | Yoneda representation for lattice ideals.
--
-- A subset /I/ of a lattice is an ideal if and only if it is a lower set 
-- that is closed under finite joins, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x \/ y/ is also in /I/.
--
-- /upper/ and /lower/ commute with /Down/:
--
-- * @lower x y = upper (Down x) (Down y)@
--
-- * @lower (Down x) (Down y) = upper x y@
--
-- /a/ is downward-closed:
--
-- * @'lower' x s && x '>=' y => 'lower' y s@
--
-- * @'lower' x s && 'lower' y s => 'connl' 'ideal' x '\/' 'connl' 'ideal' y '<=' s@
--
-- Finally /filter >>> ideal/ and /ideal >>> filter/ are both connections
-- on /a/ and /Idx a/ respectively.
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
--
type Ideal a b = (Connection a b, Eq a, (Join-Semilattice) a)
--type SetIdeal a b = Ideal (Set a) b
--type SetFilter a b = Filter a (Set b)

-- | Lower set in /b/ generated by an element in /a/.
--
lower :: Ideal a b => a -> b -> Bool
lower a b = connr connection b `joinLe` a

-- | Yoneda representation for lattice filters.
--
-- A subset /I/ of a lattice is an filter if and only if it is an upper set 
-- that is closed under finite meets, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x /\ y/ is also in /I/.
--
-- /upper/ and /lower/ commute with /Down/:
--
-- * @lower x y = upper (Down x) (Down y)@
--
-- * @lower (Down x) (Down y) = upper x y@
--
-- /b/ is upward-closed:
--
-- * @'upper' x s && x '<=' y => 'upper' y s@
--
-- * @'upper' x s && 'upper' y s => 'connl' 'filter' x '/\' 'connl' 'filter' y '>=' s@
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
--
type Filter a b = (Connection a b, Eq b, (Meet-Semilattice) b)

-- | Upper set in /a/ generated by an element in /b/.
upper :: Filter a b => b -> a -> Bool
upper b a = connl connection a `meetGe` b

---------------------------------------------------------------------
-- Connection instances
---------------------------------------------------------------------

instance Connection a a where
  connection = C.id

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

instance Connection Word8 (Lifted Integer) where
  connection = w08nat C.>>> natint

instance Connection Word8 Natural where
  connection = w08nat

instance Connection Word16 CUShort where
  connection = w16c16

instance Connection Word16 (Lifted Integer) where
  connection = w16nat C.>>> natint

instance Connection Word16 Natural where
  connection = w16nat

instance Connection Word32 CUInt where
  connection = w32c32

instance Connection Word32 (Lifted Integer) where
  connection = w32nat C.>>> natint

instance Connection Word32 Natural where
  connection = w32nat

instance Connection Word64 CULong where
  connection = w64c64

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


{-
instance Connection Float (Lowered Ordering) where
  connection = ratord

instance Triple Float (Extended Ordering) where
  triple = ratord

instance Triple Double (Extended Ordering) where
  triple = ratord

instance Triple (Ratio Integer) (Extended Ordering) where
  triple = ratord


instance Connection (Nan Int32) Float where
  connection = i32f32

instance Connection Float (Nan Int32) where
  connection = f32i32

--instance Connection Float (Nan Int64) where
--  connection = f32i32 C.>>> mapped i32i64

instance Connection Double CDouble where
  connection = f64c64

instance Connection (Nan Int64) Double where
  connection = i64f64

instance Connection Double (Nan Int64) where
  connection = f64i64

instance Connection (Nan Int) Double where
  connection = ixxf64

instance Connection Double (Nan Int) where
  connection = f64ixx

instance (Connection a b) => Connection [a] [b] where
  connection = mapped connection


mapped :: Functor f => Conn a b -> Conn (f a) (f b)
mapped (Conn f g) = Conn (fmap f) (fmap g)

instance (Join-Monoid) a => Connection () a where
  connection = Conn (const bottom) (const ())

instance (Meet-Monoid) a => Connection a () where
  connection = Conn (const ()) (const top)
-}


instance Connection a b => Connection (Down b) (Down a) where
  connection = Conn (\(Down b) -> Down $ right b) (\(Down a) -> Down $ left a)

instance (Connection a b, Connection c d) => Connection (a, c) (b, d) where
  connection = strong connection connection

instance (Connection a b, Connection c d) => Connection (Either a c) (Either b d) where
  -- |
  -- > connection :: Connection a b => Connection (Lifted a) (Lifted b) 
  -- > connection :: Connection a b => Connection (Lowered a) (Lowered b) 
  connection = choice connection connection


---------------------------------------------------------------------
-- Triple instances
---------------------------------------------------------------------

instance Triple a a where
  triple = C.id

instance Triple Double Float where
  triple = f64f32

instance Triple (Ratio Integer) Float where
  triple = ratf32

instance Triple (Ratio Integer) Double where
  triple = ratf64

{-
instance Bounded a => Triple () a where
  triple = Trip (const bottom) (const ()) (const top)

instance Triple Int8 (Extended Integer) where
  triple = i08int'

instance Triple Int16 (Extended Integer) where
  triple = i16int'

instance Triple Int32 (Extended Integer) where
  triple = i32int'

instance Triple Int64 (Extended Integer) where
  triple = i64int'

instance Triple Int (Extended Integer) where
  triple = ixxint'

instance Triple Word8 (Lowered Natural) where
  triple = w08nat'

instance Triple Word16 (Lowered Natural) where
  triple = w16nat'

instance Triple Word32 (Lowered Natural) where
  triple = w32nat'

instance Triple Word64 (Lowered Natural) where
  triple = w64nat'

instance Triple Word (Lowered Natural) where
  triple = wxxnat'

--instance Triple (Ratio Natural) (Lowered Ordering) where
--  triple = ratord

instance Triple (Ratio Natural) (Lowered Word8) where
  triple = ratwxx 255

instance Triple (Ratio Natural) (Lowered Word16) where
  triple = ratwxx 65535

instance Triple (Ratio Natural) (Lowered Word32) where
  triple = ratwxx 4294967295

instance Triple (Ratio Natural) (Lowered Word64) where
  triple = ratwxx 18446744073709551615

instance Triple (Ratio Natural) (Lowered Natural) where
  triple = ratnat

instance Triple (Ratio Integer) (Extended Int8) where
  triple = ratixx 127

instance Triple (Ratio Integer) (Extended Int16) where
  triple = ratixx 32767

instance Triple (Ratio Integer) (Extended Int32) where
  triple = ratixx 2147483647

instance Triple (Ratio Integer) (Extended Int64) where
  triple = ratixx 9223372036854775807

instance Triple (Ratio Integer) (Extended Integer) where
  triple = ratint
-}


{-
rati08 :: Trip (Ratio Integer) (Extended Int8)
rati08 = ratixx 127

rati16 :: Trip (Ratio Integer) (Extended Int16)
rati16 = ratixx 32767
rati32 :: Trip (Ratio Integer) (Extended Int32)
rati32 = ratixx 2147483647

rati64 :: Trip (Ratio Integer) (Extended Int64)
rati64 = ratixx 9223372036854775807

ratw08 :: Trip (Ratio Natural) (Lowered Word8) 
ratw08 = ratwxx 255

ratw16 :: Trip (Ratio Natural) (Lowered Word16) 
ratw16 = ratwxx 65535

ratw32 :: Trip (Ratio Natural) (Lowered Word32) 
ratw32 = ratwxx 4294967295

ratw64 :: Trip (Ratio Natural) (Lowered Word64) 
ratw64 = ratwxx 18446744073709551615

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
-}


instance Triple a (Either a a) where
  triple = Trip Left (either id id) Right

instance Lattice a => Triple (a, a) a where
  triple = Trip (uncurry (\/)) (\x -> (x,x)) (uncurry (/\))

instance (Triple a b, Triple c d) => Triple (a, c) (b, d) where
  triple = strong' triple triple

instance (Triple a b, Triple c d) => Triple (Either a c) (Either b d) where
  -- |
  -- > triple :: Triple a b => Triple (Lifted a) (Lifted b) 
  -- > triple :: Triple a b => Triple (Lowered a) (Lowered b) 
  triple = choice' triple triple

{-
--check this
instance (Triple a b, Bounded b) => Triple (Maybe a) (Either a b) where
  triple = Trip f g h where
    f = maybe (Right bottom) Left
    g = either Just (const Nothing)
    h = maybe (Right top) Left

instance (Triple a b, Bounded a) => Triple (Maybe b) (Either a b) where
  triple = Trip f g h where
    f = maybe (Left bottom) Right
    g = either (const Nothing) Just
    h = maybe (Left top) Right

instance (Triple a b) => Triple [a] [b] where
  triple = mapped' triple

instance (Triple a b) => Triple (Nan a) (Nan b) where
  triple = mapped' triple

instance (Triple a b) => Triple (Extended a) (Extended b) where
  triple = mapped' . mapped' $ triple

instance (Triple a b) => Triple (Extended a) (Extended b) where
  triple = mapped' . mapped' . mapped' $ triple

lifted :: Conn a b -> Conn (Lifted a) (Lifted b)
lifted (Conn f g) = Conn (second f) (second g)

lowered :: Conn a b -> Conn (Lowered a) (Lowered b)
lowered (Conn f g) = Conn (first f) (first g)


-}
