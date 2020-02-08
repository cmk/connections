{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE QuasiQuotes #-}
module Data.Float.Unit (
  -- * Unit
    Unit
  , unt
  , unit
  , unit'
  , untf64
  , unUnit
  , cmpl
  -- * Biunit
  , Biunit
  , bnt
  , biunit
  , biunit'
  , bntf64
  , unBiunit
) where

import Control.Applicative
import Data.Prd
import Data.Connection hiding (unit)
import Data.Group

import Data.Semiring
import Data.Semifield (ninf)
import Data.Semilattice.N5
import Data.Semilattice.Top
import Prelude hiding (Ord(..), Num(..))
import Data.Data
import Data.Text as T
import Language.Haskell.TH.Syntax (Q, Exp(..), lift, liftData, dataToExpQ)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Text.Read (readMaybe)

-- | A 'Double' in the interval \( [0,1] \).
--
newtype Unit = Unit Double deriving (Data, Show)

-- | A quasiquoter for safely constructing a 'Unit' from a constant.
--
-- >>> [unt|1.0|]
-- Unit {unUnit = 1.0}
unt :: QuasiQuoter
unt = let
    msg = "Invalid Unit: must be in [0,1]."
    clip x = if 0 <= x && x <= 1 then Just (Unit x) else Nothing
    mk s = readMaybe s >>= clip
    in qq $ justErr msg . mk

-- | Monotone 'Unit' constructor.
--
-- Clips inputs greater than 1 and maps /NaN/ to 'Nothing'.
--
unit :: N5 Double -> Bottom Unit
unit = connr untf64

-- | 'Unit' constructor.
--
-- Clips inputs outside of the interval \( [0,1] \).
--
-- /Caution/ due to /NaN/s this is not a monotone map.
--
unit' :: Double -> Unit
unit' = Unit . clipu

-- | A 'Unit' \(\dashv\) 'Double' connection.
--
-- Clips inputs greater than 1 and maps /NaN/ to 'Nothing'.
--
untf64 :: Conn (Bottom Unit) (N5 Double)
untf64 = Conn f g where
  f = maybe (N5 ninf) (N5 . unUnit)
  g (N5 x) | x >= 0 = Just . Unit $ min 1 x
           | otherwise = Nothing

unUnit :: Unit -> Double
unUnit (Unit x) = x

-- | `Unit` complement.
--
cmpl :: Unit -> Unit
cmpl (Unit x) = Unit $ 1 - x

clipu = min 1 . max 0

instance Prd Unit where
  pcompare (Unit x) (Unit y) = pcompare (clipu x) (clipu y)

instance Minimal Unit where
  minimal = Unit 0

instance Maximal Unit where
  maximal = Unit 1

-------------------------------------------------------------------------------
-- Biunit
-------------------------------------------------------------------------------

-- | A 'Double' in the interval \( [-1,1] \).
--
newtype Biunit = Biunit Double deriving (Data, Show)


-- | A quasiquoter for safely constructing a 'Biunit' from a constant.
--
-- >>> [bnt|1.0|]
-- Biunit {unBiunit = 1.0}
bnt :: QuasiQuoter
bnt = let
    msg = "Invalid Biunit: must be in [-1,1]."
    clip x = if -1 <= x && x <= 1 then Just (Biunit x) else Nothing
    mk s = readMaybe s >>= clip
    in qq $ justErr msg . mk

-- | Monotone 'Biunit' constructor.
--
biunit :: N5 Double -> Bottom Biunit
biunit = connr bntf64

-- | 'Biunit' constructor.
--
-- Clips inputs outside of the interval \( [-1,1] \).
--
-- /Caution/ due to /NaN/s this is not a monotone map.
--
biunit' :: Double -> Biunit
biunit' = Biunit . clipb

-- | A 'Biunit' \(\dashv\) 'Double' connection.
--
-- Clips inputs greater than 1 and maps /NaN/ to 'Nothing'.
--
bntf64 :: Conn (Bottom Biunit) (N5 Double)
bntf64 = Conn f g where
  f = maybe (N5 ninf) (N5 . unBiunit)
  g (N5 x) | x >= -1 = Just . Biunit $ min 1 x
           | otherwise = Nothing

unBiunit :: Biunit -> Double
unBiunit (Biunit x) = x

clipb = min 1 . max (-1)

instance Prd Biunit where
  pcompare (Biunit x) (Biunit y) = pcompare (clipb x) (clipb y)

instance Minimal Biunit where
  minimal = Biunit (-1)

instance Maximal Biunit where
  maximal = Biunit 1

instance Semigroup (Additive Biunit) where
  -- >>> biunit' one + biunit' one
  -- Biunit {unBiunit = 1.0}
  (<>) = liftA2 $ \(Biunit x) (Biunit y) -> biunit' (x + y)

instance Monoid (Additive Biunit) where
  mempty = pure $ Biunit 0
 
instance Magma (Additive Biunit) where
  (<<) = liftA2 $ \(Biunit x) (Biunit y) -> biunit' (x - y)

instance Quasigroup (Additive Biunit)
instance Loop (Additive Biunit)
instance Group (Additive Biunit)

instance Semigroup (Multiplicative Biunit) where
  (<>) = liftA2 $ \(Biunit x) (Biunit y) -> biunit' (x * y)

instance Monoid (Multiplicative Biunit) where
  mempty = pure $ Biunit 1
 
{-
instance (Multiplicative-Group) a => Magma (Multiplicative (Biunit a)) where
  (<<) = liftA2 (/)

instance (Multiplicative-Group) a => Quasigroup (Multiplicative (Biunit a))
instance (Multiplicative-Group) a => Loop (Multiplicative (Biunit a))
instance (Multiplicative-Group) a => Group (Multiplicative (Biunit a))
-}

instance Presemiring Biunit
instance Semiring Biunit
instance Ring Biunit
--instance Semifield a => Semifield (Biunit a)
--instance Field a => Field (Biunit a)

-------------------------------------------------------------------------------
-- Internal
-------------------------------------------------------------------------------

qq :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qq = qqLift liftData

justErr :: e -> Maybe a -> Either e a
justErr e = maybe (Left e) Right

-- Necessary when `Text` is involved, https://stackoverflow.com/q/38143464
qqText :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qqText = qqLift liftDataWithText
  where
    liftText :: T.Text -> Q Exp
    liftText = fmap (AppE $ VarE 'T.pack) . lift . T.unpack

    liftDataWithText :: Data a => a -> Q Exp
    liftDataWithText = dataToExpQ (fmap liftText . cast)

qqLift :: (a -> Q Exp) -> ([Char] -> Either [Char] a) -> QuasiQuoter
qqLift l f = QuasiQuoter {
    quoteExp = either fail l . f
  , quotePat = no "patterns"
  , quoteType = no "types"
  , quoteDec = no "declarations"
  }
  where no c = const (fail ("This QQ produces expressions, not " <> c))
