{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Ratio where

import Control.Applicative
import Data.Prd.Nan
import Data.Int
import Data.Word
import Data.Float
import Data.Prd
import Data.Ord
import Data.Connection
--import Data.Connection.Filter
--import Data.Connection.Float
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Data.Ratio

import Test.Data.Connection

import qualified Data.Prd.Property as Prop
import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

import qualified Test.Function.Monotone as M
import qualified Test.Function.Invertible as I

--import qualified Prelude as P
import GHC.Float as F

gen_rat' :: Gen Rational
gen_rat' = G.realFrac_ (R.linearFracFrom 0 (- 2^127) (2^127))

{- TODO get these passing
prop_connections_ratnan :: Property
prop_connections_ratnan = withTests 1000 . property $ do
  x <- forAll gen_nan'
  x' <- forAll gen_nan'
  y <- forAll $ gen_nan gen_rat
  y' <- forAll $ gen_nan gen_rat

  assert $ Prop.connection (tripl fldnan) x y
  assert $ Prop.connection (tripr fldnan) y x
  assert $ Prop.monotonel (tripl fldnan) x x'
  assert $ Prop.monotonel (tripr fldnan) y y'
  assert $ Prop.monotoner (tripl fldnan) y y'
  assert $ Prop.monotoner (tripr fldnan) x x'
  assert $ Prop.closed (tripl fldnan) x
  assert $ Prop.closed (tripr fldnan) y -- would fail on y = Def NaN
  assert $ Prop.kernel (tripl fldnan) y
  assert $ Prop.kernel (tripr fldnan) x

prop_connections_ratord :: Property
prop_connections_ratord = withTests 1000 . property $ do
  x <- forAll gen_nan'
  x' <- forAll gen_nan'
  y <- forAll $ gen_nan gen_ord
  y' <- forAll $ gen_nan gen_ord

  let ratord = fldord :: Trip Rational (Nan Ordering)

  assert $ Prop.connection (tripl ratord) x y
  assert $ Prop.connection (tripr ratord) y x
  assert $ Prop.monotonel (tripl ratord) x x'
  assert $ Prop.monotonel (tripr ratord) y y'
  assert $ Prop.monotoner (tripl ratord) y y'
  assert $ Prop.monotoner (tripr ratord) x x'
  assert $ Prop.closed (tripl ratord) x
  assert $ Prop.closed (tripr ratord) y
  assert $ Prop.kernel (tripl ratord) y
  assert $ Prop.kernel (tripr ratord) x
-}

prop_connections_ratf32 :: Property
prop_connections_ratf32 = withTests 10000 . property $ do
  x <- forAll gen_nan'
  x' <- forAll gen_nan'
  y <- forAll gen_f32
  y' <- forAll gen_f32
{-
  assert $ Prop.connection ratf32' x y
  assert $ Prop.monotoner ratf32' y y' 
  --assert $ Prop.monotonel ratf32' x x'
  assert $ Prop.closed ratf32' x
  assert $ Prop.kernel ratf32' y
-}

  assert $ Prop.connection (tripl ratf32) x y
  assert $ Prop.connection (tripr ratf32) y x
  assert $ Prop.monotoner (tripl ratf32) y y'
  --assert $ Prop.monotoner (tripr ratf32) x x'
  --assert $ Prop.monotonel (tripl ratf32) x x' -- hedgehog exception?
  assert $ Prop.monotonel (tripr ratf32) y y'
  --assert $ Prop.closed (tripl ratf32) x -- hedgehog exception?
  assert $ Prop.closed (tripr ratf32) y
  assert $ Prop.kernel (tripl ratf32) y
  --assert $ Prop.kernel (tripr ratf32) x -- x = (-1) % 25, (-1) % (-31)

tests :: IO Bool
tests = checkParallel $$(discover)
