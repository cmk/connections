{-# Language AllowAmbiguousTypes #-}

module Data.Connection.Ratio where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Int
import Data.Prd.Nan
import Data.Word
import Data.Float
import Data.Prd
import Data.Function (on)
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import GHC.Num (subtract)
import qualified Data.Bits as B
import qualified GHC.Float as F
import qualified GHC.Float.RealFracMethods as R

import Prelude
import qualified Control.Category as C

import Data.Ratio

import GHC.Real

class Prd a => TripRational a where
  tripRational :: Trip Rational a

-- | Lawful replacement for the version in base.
--
fromRational :: TripRational a => Rational -> a
fromRational = connl . tripl $ tripRational

instance TripRational Rational where
  tripRational = C.id

instance TripRational Float where
  tripRational = ratf32
