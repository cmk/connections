{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE QuasiQuotes #-}
module Data.Float.Unit where

import Data.Prd
import Data.Connection hiding (unit)
import Data.Semifield (ninf)
import Prelude hiding (Ord(..))
import Data.Data
import Data.Text as T
import Language.Haskell.TH.Syntax (Q, Exp(..), lift, liftData, dataToExpQ)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Text.Read (readMaybe)
{-
untbnt
f64unt
posunt
sgnbnt
-}

-- | A 'Double' in the interval \( [0,1] \).
--
newtype Unit = Unit { fromUnit :: Double } deriving (Data, Show)


instance Prd Unit where
  pcompare (Unit x) (Unit y) = pcompare x y


-- | 
--
-- Clips inputs greater than 1.
--
untf64 :: Conn (Maybe Unit) Double
untf64 = Conn f g where
  f = maybe ninf fromUnit
  g x | x >= 0 = Just . Unit $ min 1 x
      | otherwise = Nothing


-- | Safe `Unit` complement
complement :: Unit -> Unit
complement (Unit a) = Unit $ 1 - a

unit :: Double -> Maybe Unit
unit = connr untf64

unit' :: Double -> Unit
unit' = Unit . min 1 . max 0

-- | A quasiquoter for safely constructing a 'Unit' from a constant.
--
-- >>> [unt|1.0|]
-- Unit {fromUnit = 1.0}
unt :: QuasiQuoter
unt = let
    msg = "Invalid Unit: must be in [0,1]."
    clip x = if 0 <= x && x <= 1 then Just (Unit x) else Nothing
    mk s = readMaybe s >>= clip
    in qq $ justErr msg . mk

-------------------------------------------------------------------------------
-- Biunit
-------------------------------------------------------------------------------

-- | A 'Double' in the interval \( [-1,1] \).
--
newtype Biunit = Biunit { fromBiunit :: Double } deriving (Data, Show)

instance Prd Biunit where
  pcompare (Biunit x) (Biunit y) = pcompare x y

-- | 
--
-- Clips inputs greater than 1.
--
bntf64 :: Conn (Maybe Biunit) Double
bntf64 = Conn f g where
  f = maybe ninf fromBiunit
  g x | x >= -1 = Just . Biunit $ min 1 x
      | otherwise = Nothing

biunit :: Double -> Maybe Biunit
biunit = connr bntf64

biunit' :: Double -> Biunit
biunit' = Biunit . min 1 . max (-1)

-- | A quasiquoter for safely constructing a 'Biunit' from a constant.
--
-- >>> [bnt|1.0|]
-- Biunit {fromBiunit = 1.0}
bnt :: QuasiQuoter
bnt = let
    msg = "Invalid Biunit: must be in [-1,1]."
    clip x = if -1 <= x && x <= 1 then Just (Biunit x) else Nothing
    mk s = readMaybe s >>= clip
    in qq $ justErr msg . mk


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
