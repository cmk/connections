module Data.Connection.Float where

import Control.Category ((>>>))
import Data.Bits ((.&.))
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Prd.Nan
import Data.Function (on)
import Data.Connection
import Data.Connection.Int
import Data.Connection.Word
import Data.Connection.Ratio
import GHC.Num (subtract)
import qualified Data.Bits as B
import qualified GHC.Float as F
import qualified GHC.Float.RealFracMethods as R

import Prelude
import qualified Control.Category as C

import Data.Ratio

import GHC.Real



class Prd a => ConnFloat a where
  connFloat :: Conn Float a

instance ConnFloat Float where
  connFloat = C.id

instance ConnFloat (Nan Int32) where
  connFloat = f32i32

instance ConnFloat (Nan Ordering) where
  connFloat = tripl fldord

instance ConnFloat Ulp32 where
  connFloat = f32u32

--instance ConnFloat (Nan Word8) where
--  connFloat = tripl f32w08


class Prd a => ConnDouble a where
  connDouble :: Conn Double a

instance ConnDouble Double where
  connDouble = C.id

--instance ConnDouble Ulp64 where
--  connDouble = f64u64

instance ConnDouble (Nan Int64) where
  connDouble = f64i64




