{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language DataKinds           #-}
{-# Language Safe                #-}
{-# Language ViewPatterns        #-}
{-# Language PatternSynonyms     #-}
{-# Language RankNTypes          #-}
{-# Language QuantifiedConstraints #-}

module Data.Connection (
  -- * Types
    Kan(..)
  , Conn()
  , (\|/)
  , (/|\)
  -- * Connection L
  , type ConnL
  , pattern ConnL
  , connL
  , swapL
  , embedL
  , ceiling
  , ceiling1
  , ceiling2
  , filterL
  , minimal
  , bottom
  , join
  , joins
  , (\/)
  , (//)
  , neg
  , middle
  , equivL
  -- * Connection R
  , type ConnR
  , pattern ConnR
  , connR
  , swapR
  , floor
  , floor1
  , floor2
  , embedR
  , filterR
  , maximal
  , top
  , meet
  , meets
  , (/\)
  , (\\)
  , non
  , boundary
  , equivR
  -- * Connection
  , Triple
  , Lattice
  , Biheyting
  , type Trip
  , pattern Conn
  , half
  , midpoint
  , round
  , round1
  , round2
  , truncate
  , truncate1
  , truncate2
  , glb, lub
  -- * Classes
  , Semilattice
  , Extremal
  , Bounded
  , Heyting(..)
  , Connection(..)
  , ConnFloat
  , ConnDouble
  , ConnInteger
  , ConnRational
  , ConnExtended
) where

import safe Data.Connection.Conn
import safe Data.Connection.Class
import safe Data.Lattice
import safe Data.Order
import safe Prelude hiding
  (Bounded,fromInteger, fromRational, floor, ceiling, round, truncate)

-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Int
-- >>> import Prelude hiding (Ord(..), Bounded, fromInteger, fromRational, RealFrac(..))
-- >>> import qualified Prelude as P
-- >>> :load Data.Connection

-- | Determine which half of the interval between 2 representations of /a/ a particular value lies.
-- 
-- @ 'half' t x = 'pcompare' (x - 'counitR' t x) ('unitL' t x - x) @
--
half :: (Num a, Preorder a) => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - counitR t x) (unitL t x - x) 

-- | Return the midpoint of the interval containing x.
--
-- >>> midpoint f32i08 4.3
-- 4.5
-- >>> midpoint f64i08 4.3
-- 4.5
-- >>> pi - midpoint f64f32 pi
-- 3.1786509424591713e-8
--
-- >>> maybe False (~~ EQ) $ half f64f32 (midpoint f64f32 pi)
-- True
--
midpoint :: Fractional a => Trip a b -> a -> a
midpoint t x = counitR t x / 2 + unitL t x / 2

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | Return the nearest value to x.
--
-- > round @a @a = id
-- 
-- If x lies halfway between two finite values, then return the value
-- with the larger absolute value (i.e. round away from zero).
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
-- Usable in conjunction with /RebindableSyntax/:
--
-- >>> fromRational = round
-- >>> fromRational @Float 1.3
-- 1.3
-- >>> fromRational @Float (1 :% 0)
-- Infinity
-- >>> fromRational @Float (0 :% 0)
-- NaN
--
round :: forall a b. (Num a, Triple a b) => a -> b
round x = case pcompare halfR halfL of
  Just GT -> ceiling x
  Just LT -> floor x
  _       -> truncate x

  where
    halfR = x - counitR (connR @a @b) x -- dist from lower bound

    halfL = unitL (connL @a @b) x - x -- dist from upper bound

-- | Lift a unary function over a 'Trip'.
--
-- Results are rounded to the nearest value with ties away from 0.
--
round1 :: forall a b. (Num a, Triple a b) => (a -> a) -> b -> b
round1 f x = round $ f (g x) where Conn _ g _ = connL
{-# INLINE round1 #-}

-- | Lift a binary function over a 'Trip'.
--
-- Results are rounded to the nearest value with ties away from 0.
--
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
--
round2 :: (Num a, Triple a b) => (a -> a -> a) -> b -> b -> b
round2 f x y = round $ f (g x) (g y) where Conn _ g _ = connL
{-# INLINE round2 #-}

-- | Truncate towards zero.
--
-- > truncate @a @a = id
--
truncate :: (Num a, Triple a b) => a -> b
truncate x = if x >~ 0 then floor x else ceiling x

-- | Lift a unary function over a 'Trip'.
--
-- Results are truncated towards 0.
--
truncate1 :: (Num a, Triple a b) => (a -> a) -> b -> b
truncate1 f x = truncate $ f (g x) where Conn _ g _ = connL
{-# INLINE truncate1 #-}

-- | Lift a binary function over a 'Trip'.
--
-- Results are truncated towards 0.
--
truncate2 :: (Num a, Triple a b) => (a -> a -> a) -> b -> b -> b
truncate2 f x y = truncate $ f (g x) (g y) where Conn _ g _ = connL
{-# INLINE truncate2 #-}
