{-# Language AllowAmbiguousTypes #-}

module Data.Connection.Ratio where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Connection
import Data.Connection.Float
import Data.Connection.Int
import Data.Prd
import Data.Prd.Nan
import Data.Int
import Data.Ratio
import Data.Float
import qualified Control.Category as C
import qualified GHC.Float as F
import Data.Semilattice
import Data.Semilattice.Bounded
import Data.Semiring
import Data.Semifield
import Prelude hiding (Num(..), Fractional(..), (^), Bounded)
import qualified Prelude as P
import GHC.Real hiding ((/), (^))

-- | Lawful replacement for the version in base.
--
fromRational :: TripRational a => Rational -> a
fromRational = connl . tripl $ tripRational

class Prd a => TripRational a where
  tripRational :: Trip Rational a

instance TripRational Rational where
  tripRational = C.id

instance TripRational Float where
  tripRational = ratf32

instance TripRational Double where
  tripRational = ratf64

instance TripRational (Extended Int8) where
  tripRational = rati08

instance TripRational (Extended Int16) where
  tripRational = rati16

instance TripRational (Extended Int32) where
  tripRational = rati32

instance TripRational (Extended Int64) where
  tripRational = rati64

instance TripRational (Extended Integer) where
  tripRational = ratint

cancel (x :% y) = if x < 0 && y < 0 then (abs x) :% (abs y) else x :% y

rati08 :: Trip Rational (Extended Int8) 
rati08 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x `gt` imax = Top
      | x =~ ninf = Bot
      | x `lt` imin = Fin minimal
      | otherwise = Fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x `gt` imax = Fin maximal
      | x `lt` imin = Bot
      | otherwise = Fin $ P.floor $ cancel x

  imax = 127

  imin = -128

rati16 :: Trip Rational (Extended Int16) 
rati16 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x `gt` imax = Top
      | x =~ ninf = Bot
      | x `lt` imin = Fin minimal
      | otherwise = Fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x `gt` imax = Fin maximal
      | x `lt` imin = Bot
      | otherwise = Fin $ P.floor $ cancel x

  imax = 32767

  imin = -32768

rati32 :: Trip Rational (Extended Int32) 
rati32 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x `gt` imax = Top
      | x =~ ninf = Bot
      | x `lt` imin = Fin minimal
      | otherwise = Fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x `gt` imax = Fin maximal
      | x `lt` imin = Bot
      | otherwise = Fin $ P.floor $ cancel x

  imax = 2147483647 

  imin = -2147483648

rati64 :: Trip Rational (Extended Int64) 
rati64 = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x `gt` imax = Top
      | x =~ ninf = Bot
      | x `lt` imin = Fin minimal
      | otherwise = Fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x `gt` imax = Fin maximal
      | x `lt` imin = Bot
      | otherwise = Fin $ P.floor $ cancel x
 
  imax = 9223372036854775807

  imin = -9223372036854775808

ratint :: Trip Rational (Extended Integer)
ratint = Trip (liftNan f) (nan' g) (liftNan h) where
  f x | x =~ pinf = Top
      | x =~ ninf = Bot
      | otherwise = Fin $ P.ceiling $ cancel x

  g = bounded ninf P.fromIntegral pinf

  h x | x =~ pinf = Top
      | x =~ ninf = Bot
      | otherwise = Fin $ P.floor $ cancel x

--maybe (127 :% 1) id . pmin (127 :% 1) . maybe (-128 :% 1) id . pmax (-128 :% 1)

-- TODO: 
-- * handle underflow / overflow / loss of precision
-- * try using 'properFraction'
ratf32 :: Trip Rational Float
ratf32 = Trip f g h
  where h (0 :% 0) = 0/0
        h (x :% 0) = if x > 0 then 1/0 else (-1/0)
        h x = P.fromRational x --F.fromRat' x

        g x | F.isFloatNaN x == 1 = 0 :% 0
            | F.isFloatInfinite x == 1 = if x > 0 then (1 :% 0) else (-1 :% 0)
            | otherwise = toRational x

        -- fix / remove
        help x = case pcompare x 0 of
                   Just LT -> shiftf (-1) x
                   Just EQ -> x
                   Just GT -> shiftf 1 x
                   Nothing -> 0/0

        f x = let y = h x in if g y `ne` x then help y else y

ratf64 :: Trip Rational Double
ratf64 = Trip h g h
  where h (0 :% 0) = 0/0
        h (x :% 0) = if x > 0 then 1/0 else (-1/0)
        h x = P.fromRational x --F.fromRat' x

        g x | F.isDoubleNaN x == 1 = 0 :% 0
            | F.isDoubleInfinite x == 1 = if x > 0 then (1 :% 0) else (-1 :% 0)
            | otherwise = toRational x
{-
        -- fix / remove
        help x = case pcompare x 0 of
                   Just LT -> shift (-1) x
                   Just EQ -> x
                   Just GT -> shift 1 x
                   Nothing -> 0/0

        f x = let y = h x in if g y `ne` x then help y else y
-}


