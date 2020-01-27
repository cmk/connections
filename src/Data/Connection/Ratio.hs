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

class Prd a => ConnRational a where
  connRational :: Conn Rational a

-- | Lawful replacement for the version in base.
--
fromRational :: ConnRational a => Rational -> a
fromRational = connl connRational

instance ConnRational Rational where
  connRational = C.id

instance ConnRational Float where
  connRational = tripl ratf32
