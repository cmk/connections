{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language DataKinds           #-}
{-# Language Safe                #-}
{-# Language ViewPatterns        #-}
{-# Language PatternSynonyms     #-}
{-# Language RankNTypes          #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE StandaloneDeriving  #-}

module Data.Connection.Class (
  -- * Types
    Kan(..)
  , Conn()
  , Semilattice
  , Extremal
  , ConnFloat
  , ConnDouble
  , ConnInteger
  , ConnRational
  , ConnExtended
  -- * Connection L
  , ConnL
  , pattern ConnL
  , connL
  , swapL
  , embedL
  , ceiling
  , ceiling1
  , ceiling2
  , filterL
  , minimal
  , (\/)
  , glb
  -- * Connection R
  , ConnR
  , pattern ConnR
  , connR
  , swapR
  , floor
  , floor1
  , floor2
  , embedR
  , filterR
  , maximal
  , (/\)
  , lub
  -- * Connection k
  , Trip
  , pattern Conn
  , maybeL
  , maybeR
  , choice
  , strong
  , fmapped
  -- * Connection
  , Connection(..)
  , Triple
) where

import safe Control.Applicative (liftA2)
import safe Control.Category ((>>>))
import safe Data.Bool (bool)
import safe Data.Connection.Conn
import safe Data.Connection.Int
import safe Data.Connection.Word
import safe Data.Connection.Float
import safe Data.Connection.Double
import safe Data.Connection.Ratio
import safe Data.Functor.Contravariant
import safe Data.Functor.Identity
import safe Data.Monoid
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Interval
import safe Data.Word
import safe Data.Int
import safe GHC.TypeNats
import safe Numeric.Natural
import safe Prelude hiding (Bounded, floor, ceiling, fromInteger, fromRational)
import safe qualified Control.Category as C
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set
import safe qualified Data.Finite as F
import safe qualified Data.Universe.Class as U
import safe qualified Prelude as P

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection


-- | Semilattices.
--
-- A complete is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- These operations may in turn be defined by the lower and upper adjoints to the unique
-- function /a -> (a, a)/.
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) = (x '\/' y) '\/' z
-- x '/\' (y '/\' z) = (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y = y '\/' x
-- x '/\' y = y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x = x
-- x '/\' x = x
-- @
--
-- /Absorption/
--
-- @
-- (x '\/' y) '/\' y = y
-- (x '/\' y) '\/' y = y
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law Absorption >.
--
-- Note that distributivity is _not_ a requirement for a complete.
-- However when /a/ is distributive we have;
-- 
-- @
-- 'glb' x y z = 'lub' x y z
-- @
--
-- See < https://en.wikipedia.org/wiki/Lattice_(order) >.
--
type Semilattice k a = Connection k (a, a) a

type Extremal k = Connection k ()

type ConnInteger k = Connection k (Maybe Integer)

type ConnFloat k = Connection k Float

type ConnDouble k = Connection k Double

type ConnRational k = Connection k Rational

type ConnExtended k a b = Connection k a (Extended b)

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

-- | A constraint kind representing an <https://ncatlab.org/nlab/show/adjoint+triple adjoint triple> of Galois connections.
--
type Triple a b = (Connection 'L a b, Connection 'R a b)



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

-- | Obtain the principal filter in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an filter if and only if it is an upper set 
-- that is closed under finite meets, i.e., it is nonempty and for all 
-- /x/, /y/ in /B/, the element @x /\ y@ is also in /b/.
--
-- /filterL/ and /filterR/ commute with /Down/:
--
-- > filterL a b <=> filterR (Down a) (Down b)
--
-- > filterL (Down a) (Down b) <=> filterR a b
--
-- /filterL a/ is upward-closed for all /a/:
--
-- > a <= b1 && b1 <= b2 => a <= b2
--
-- > a1 <= b && inf a2 <= b => ceiling a1 /\ ceiling a2 <= b
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
--
filterL :: Connection 'L a b => a -> b -> Bool
filterL a b = ceiling a <~ b

-- | A minimal element of a preorder defined by a connection with '()'.
--
-- 'minimal' needn't be unique, but we must have:
--
-- > x <~ minimal => x ~~ minimal
--
minimal :: Extremal 'L a => a
minimal = lowerL connL ()

infixr 5 \/

-- | Semigroup operation on a join-semilattice.
--
-- > (\/) = curry $ lowerL forked
--
(\/) :: Semilattice 'L a => a -> a -> a
(\/) = curry $ lowerL connL

-- | Greatest lower bound operator.
--
-- > glb x x y = x
-- > glb x y z = glb z x y
-- > glb x x y = x
-- > glb x y z = glb x z y
-- > glb (glb x w y) w z = glb x w (glb y w z)
--
-- >>> glb 1.0 9.0 7.0
-- 7.0
-- >>> glb 1.0 9.0 (0.0 / 0.0)
-- 9.0
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
glb :: Triple (a, a) a => a -> a -> a -> a
glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

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

-- | Obtain the principal ideal in /B/ generated by an element of /A/.
--
-- A subset /B/ of a lattice is an ideal if and only if it is a lower set 
-- that is closed under finite joins, i.e., it is nonempty and for all 
-- /x/, /y/ in /B/, the element /x \/ y/ is also in /B/.
--
-- /filterR a/ is downward-closed for all /a/:
--
-- > a >= b1 && b1 >= b2 => a >= b2
--
-- > a1 >= b && a2 >= b => floor a1 \/ floor a2 >= b
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
--
filterR :: Connection 'R a b => a -> b -> Bool
filterR a b = b <~ floor a

-- | A maximal element of a preorder defined by a connection with '()'.
--
-- 'maximal' needn't be unique, but we must have:
--
-- > x >~ maximal => x ~~ maximal
--
maximal :: Extremal 'R a => a
maximal = upperR connR ()

infixr 6 /\ -- comment for the parser

-- | Semigroup operation on a meet-semilattice.
--
-- > (/\) = curry $ upperR forked
--
(/\) :: Semilattice 'R a => a -> a -> a
(/\) = curry $ upperR connR

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
--
lub :: Triple (a, a) a => a -> a -> a -> a
lub x y z = (x /\ y) \/ (y /\ z) \/ (z /\ x)

---------------------------------------------------------------------
-- Connection
---------------------------------------------------------------------

maybeL :: Triple () b => Trip (Maybe a) (Either a b)
maybeL = trip f g h where
  f = maybe (Right minimal) Left
  g = either Just (const Nothing)
  h = maybe (Right maximal) Left

maybeR :: Triple () a => Trip (Maybe b) (Either a b)
maybeR = trip f g h where
  f = maybe (Left minimal) Right
  g = either (const Nothing) Just
  h = maybe (Left maximal) Right

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

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

fork :: a -> (a, a)
fork x = (x, x)

semilatticeN5 :: (Total a, Fractional a) => Conn k (a, a) a
semilatticeN5 = Conn (uncurry joinN5) fork (uncurry meetN5) where
  joinN5 x y = maybe (1 / 0) (bool y x . (>= EQ)) (pcompare x y)

  meetN5 x y = maybe (-1 / 0) (bool y x . (<= EQ)) (pcompare x y)

extremalN5 :: (Total a, Fractional a) => Conn k () a
extremalN5 = Conn (const $ -1/0) (const ()) (const $ 1/0)

semilatticeOrd :: (Total a) => Conn k (a, a) a
semilatticeOrd = Conn (uncurry max) fork (uncurry min)

extremalOrd :: (Total a, P.Bounded a) => Conn k () a
extremalOrd = Conn (const minBound) (const ()) (const maxBound)

instance Connection k ((),()) () where conn = semilatticeOrd
instance Connection k (Bool, Bool) Bool where conn = semilatticeOrd
instance Connection k () Bool where conn = extremalOrd
instance Connection k (Ordering, Ordering) Ordering  where conn = semilatticeOrd
instance Connection k () Ordering where conn = extremalOrd

instance Connection k (Word8, Word8) Word8 where conn = semilatticeOrd
instance Connection k () Word8 where conn = extremalOrd
instance Connection k (Word16, Word16) Word16 where conn = semilatticeOrd
instance Connection k () Word16 where conn = extremalOrd
instance Connection k (Word32, Word32) Word32 where conn = semilatticeOrd
instance Connection k () Word32 where conn = extremalOrd
instance Connection k (Word64, Word64) Word64 where conn = semilatticeOrd
instance Connection k () Word64 where conn = extremalOrd
instance Connection k (Word, Word) Word where conn = semilatticeOrd
instance Connection k () Word where conn = extremalOrd
instance Connection k (Natural, Natural) Natural where conn = semilatticeOrd

instance Connection k (Positive, Positive) Positive where conn = semilatticeN5
instance Connection k () Positive where
  conn = Conn (const $ 0 :% 1) (const ()) (const $ 1 :% 0)

instance Connection k (Int8, Int8) Int8 where conn = semilatticeOrd
instance Connection k () Int8 where conn = extremalOrd
instance Connection k (Int16, Int16) Int16 where conn = semilatticeOrd
instance Connection k () Int16 where conn = extremalOrd
instance Connection k (Int32, Int32) Int32 where conn = semilatticeOrd
instance Connection k () Int32 where conn = extremalOrd
instance Connection k (Int64, Int64) Int64 where conn = semilatticeOrd
instance Connection k () Int64 where conn = extremalOrd
instance Connection k (Int, Int) Int where conn = semilatticeOrd
instance Connection k () Int where conn = extremalOrd
instance Connection k (Integer, Integer) Integer where conn = semilatticeOrd

instance Connection k (Rational, Rational) Rational where conn = semilatticeN5
instance Connection k () Rational where
  conn = Conn (const $ -1 :% 0) (const ()) (const $ 1 :% 0)

instance Connection k (F.Finite n, F.Finite n) (F.Finite n) where conn = semilatticeOrd
instance KnownNat n => Connection k () (F.Finite n) where conn = extremalOrd

instance Connection k (Float, Float) Float where conn = semilatticeN5
instance Connection k () Float where conn = extremalN5

instance Connection k (Double, Double) Double where conn = semilatticeN5
instance Connection k () Double where conn = extremalN5

instance Total a => Connection k (Set.Set a, Set.Set a) (Set.Set a) where
  conn = Conn (uncurry Set.union) fork (uncurry Set.intersection)

--instance (Total a, U.Finite a) => Connection k () (Set.Set a) where
--  conn = Conn (const Set.empty) (const ()) (const $ Set.fromList U.universeF)
instance (Total a) => Connection 'L () (Set.Set a) where
  conn = ConnL (const Set.empty) (const ())

instance (Total a, U.Finite a) => Connection 'R () (Set.Set a) where
  conn = ConnR (const ()) (const $ Set.fromList U.universeF)

instance Connection k (IntSet.IntSet, IntSet.IntSet) IntSet.IntSet where
  conn = Conn (uncurry IntSet.union) fork (uncurry IntSet.intersection)

instance Connection k () IntSet.IntSet where
  conn = Conn (const IntSet.empty) (const ()) (const $ IntSet.fromList U.universeF)

instance (Total a, Connection 'L (b,b) b) => Connection 'L (Map.Map a b, Map.Map a b) (Map.Map a b) where
  conn = ConnL (uncurry $ Map.unionWith (\/)) fork

instance (Total a, Connection 'R (b,b) b) => Connection 'R (Map.Map a b, Map.Map a b) (Map.Map a b) where
  conn = ConnR fork (uncurry $ Map.intersectionWith (/\))

instance (Total a, Preorder b) => Connection 'L () (Map.Map a b) where
  conn = ConnL (const Map.empty) (const ()) 

instance (Total a, U.Finite a, Connection 'R () b) => Connection 'R () (Map.Map a b) where
  conn = ConnR (const ()) (const . Map.fromList $ U.universeF `zip` repeat maximal)

instance Connection 'L (a,a) a => Connection 'L (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
  conn = ConnL (uncurry $ IntMap.unionWith (\/)) fork

instance Connection 'R (a,a) a => Connection 'R (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
  conn = ConnR fork (uncurry $ IntMap.intersectionWith (/\))

instance Preorder a => Connection 'L () (IntMap.IntMap a) where
  conn = ConnL (const IntMap.empty) (const ())

instance Connection 'R () a => Connection 'R () (IntMap.IntMap a) where
  conn = ConnR (const ()) (const . IntMap.fromList $ U.universeF `zip` repeat maximal)

joinMaybe :: Connection 'L (a, a) a => Maybe a -> Maybe a -> Maybe a
joinMaybe (Just x) (Just y) = Just (x \/ y)
joinMaybe u@(Just _) _ = u
joinMaybe _ u@(Just _) = u
joinMaybe Nothing Nothing = Nothing

meetMaybe :: Connection 'R (a, a) a => Maybe a -> Maybe a -> Maybe a
meetMaybe Nothing Nothing = Nothing
meetMaybe Nothing _ = Nothing
meetMaybe _ Nothing = Nothing
meetMaybe (Just x) (Just y) = Just (x /\ y)

instance Connection 'L (a, a) a => Connection 'L (Maybe a, Maybe a) (Maybe a) where
  conn = ConnL (uncurry joinMaybe) fork

instance Connection 'R (a, a) a => Connection 'R (Maybe a, Maybe a) (Maybe a) where
  conn = ConnR fork (uncurry meetMaybe)

instance Preorder a => Connection 'L () (Maybe a) where
  conn = ConnL (const Nothing) (const ())

instance Connection 'R () a => Connection 'R () (Maybe a) where
  conn = ConnR (const ()) (const $ Just maximal)

joinExtended :: Connection 'L (a, a) a => Extended a -> Extended a -> Extended a
joinExtended Top          _            = Top
joinExtended _            Top          = Top
joinExtended (Extended x) (Extended y) = Extended (x \/ y)
joinExtended Bottom       y            = y
joinExtended x            Bottom       = x

meetExtended :: Connection 'R (a, a) a => Extended a -> Extended a -> Extended a
meetExtended Top          y            = y
meetExtended x            Top          = x
meetExtended (Extended x) (Extended y) = Extended (x /\ y)
meetExtended Bottom       _            = Bottom
meetExtended _            Bottom       = Bottom

instance Connection 'L (a, a) a => Connection 'L (Extended a, Extended a) (Extended a) where
  conn = ConnL (uncurry joinExtended) fork

instance Connection 'R (a, a) a => Connection 'R (Extended a, Extended a) (Extended a) where
  conn = ConnR fork (uncurry meetExtended)

instance Preorder a => Connection k () (Extended a) where
  conn = Conn (const Bottom) (const ()) (const Top)

joinEither :: (Connection 'L (a, a) a, Connection 'L (b, b) b) => Either a b -> Either a b -> Either a b
joinEither (Right x) (Right y) = Right (x \/ y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x \/ y)

meetEither :: (Connection 'R (a, a) a, Connection 'R (b, b) b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x /\ y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x /\ y)

-- | All minimal elements of the upper lattice cover all maximal elements of the lower lattice.
instance (Connection 'L (a,a) a, Connection 'L (b,b) b) => Connection 'L (Either a b, Either a b) (Either a b) where
  conn = ConnL (uncurry joinEither) fork

instance (Connection 'R (a,a) a, Connection 'R (b,b) b) => Connection 'R (Either a b, Either a b) (Either a b) where
  conn = ConnR fork (uncurry meetEither)

instance (Connection 'L () a, Preorder b) => Connection 'L () (Either a b) where
  conn = ConnL (const $ Left minimal) (const ())

instance (Preorder a, Connection 'R () b) => Connection 'R () (Either a b) where
  conn = ConnR (const ()) (const $ Right maximal)

joinTuple :: (Connection 'L (a, a) a, Connection 'L (b, b) b) => (a, b) -> (a, b) -> (a, b)
joinTuple (x1, y1) (x2, y2) = (x1 \/ x2, y1 \/ y2)

meetTuple :: (Connection 'R (a, a) a, Connection 'R (b, b) b) => (a, b) -> (a, b) -> (a, b)
meetTuple (x1, y1) (x2, y2) = (x1 /\ x2, y1 /\ y2)

instance (Triple (a, a) a, Triple (b, b) b) => Connection k ((a, b), (a, b)) (a, b) where
  conn = Conn (uncurry joinTuple) fork (uncurry meetTuple)

instance (Triple () a, Triple () b) => Connection k () (a, b) where
  conn = Conn (const (minimal, minimal)) (const ()) (const (maximal, maximal))

instance (U.Finite a, Triple (b, b) b) => Connection k (a -> b, a -> b) (a -> b) where
  conn = Conn (uncurry $ liftA2 (\/)) fork (uncurry $ liftA2 (/\))

instance (U.Finite a, Triple () b) => Connection k () (a -> b) where
  conn = Conn (const $ pure minimal) (const ()) (const $ pure maximal)

instance (U.Finite a, Triple (a, a) a) => Connection k (Endo a, Endo a) (Endo a) where
  conn = Conn (\(Endo x, Endo y) -> Endo $ x\/y) fork (\(Endo x, Endo y) -> Endo $ x/\y)

instance (U.Finite a, Triple () a) => Connection k () (Endo a) where
  conn = Conn (const $ Endo minimal) (const ()) (const $ Endo maximal)

instance (U.Finite a, Triple (b, b) b) => Connection k (Op b a, Op b a) (Op b a) where
  conn = Conn (\(Op x, Op y) -> Op $ x\/y) fork (\(Op x, Op y) -> Op $ x/\y)

instance (U.Finite a, Triple () b) => Connection k () (Op b a) where
  conn = Conn (const $ Op minimal) (const ()) (const $ Op maximal)

instance U.Finite a => Connection k (Predicate a, Predicate a) (Predicate a) where
  conn = Conn (\(Predicate x, Predicate y) -> Predicate $ x\/y) fork (\(Predicate x, Predicate y) -> Predicate $ x/\y)

instance U.Finite a => Connection k () (Predicate a) where
  conn = Conn (const $ Predicate minimal) (const ()) (const $ Predicate maximal)

{-
instance (Applicative m, Connection k r) => Connection k (ContT r m a) where
  (<>) = liftA2 joinCont

instance (Applicative m, Connection k () r) => Connection k () (ContT r m a) where
  mempty = pure . ContT . const $ pure bottom

instance Monad m => Connection k (SelectT r m a) where
  (<>) = liftA2 joinSelect

instance MonadPlus m => Connection k () (SelectT r m a)) where
  bottom = pure empty
instance (Ord.Ord a, Preorder a, Preorder r, Finite r) => Preorder (Cont r a) where
  (ContT x) <~ (ContT y) = x `contLe` y

instance (Ord.Ord a, Preorder a, Preorder r, Finite r) => Preorder (Select r a) where
  (SelectT x) <~ (SelectT y) = x `contLe` y
instance (Applicative m, Total a, Preorder r, Finite r, Connection 'L r) => Connection 'L (ContT r m a, ContT r m a) (ContT r m a) where
  conn = ConnL (uncurry joinCont) fork

joinCont :: (Applicative m, Connection 'L (r,r) r) => ContT r m a -> ContT r m a -> ContT r m a
joinCont (ContT f) (ContT g) = ContT $ \p -> liftA2 join (f p) (g p) 

instance (Monad m, Total a, Preorder r, Finite r, Extremal 'L r) => Connection 'L (SelectT r m a, SelectT r m a) (SelectT r m a) where
  conn = ConnL (uncurry joinSelect) fork

joinSelect :: (Monad m, Extremal 'L r) => SelectT r m b -> SelectT r m b -> SelectT r m b
joinSelect x y = branch x y >>= id
  where
    ifM c x y = c >>= \b -> if b then x else y
    branch x y = SelectT $ \p -> ifM ((~~ maximal) <$> p x) (pure x) (pure y)
  
-}
