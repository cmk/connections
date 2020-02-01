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
import Data.Connection.Ratio
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

prop_connection_ratnan :: Property
prop_connection_ratnan = withTests 1000 . property $ do
  x <- forAll gen_rat
  x' <- forAll gen_rat
  y <- forAll $ gen_nan gen_rat'
  y' <- forAll $ gen_nan gen_rat'

  assert $ Prop.connection (tripl fldnan) x y
  assert $ Prop.connection (tripr fldnan) y x
  assert $ Prop.monotonel (tripl fldnan) x x'
  assert $ Prop.monotonel (tripr fldnan) y y'
  assert $ Prop.monotoner (tripl fldnan) y y'
  assert $ Prop.monotoner (tripr fldnan) x x'
  assert $ Prop.closed (tripl fldnan) x
  assert $ Prop.closed (tripr fldnan) y -- NB: would fail on y = Def NaN
  assert $ Prop.kernel (tripl fldnan) y
  assert $ Prop.kernel (tripr fldnan) x

prop_connection_ratord :: Property
prop_connection_ratord = withTests 1000 . property $ do
  x <- forAll gen_rat
  x' <- forAll gen_rat
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

--TODO check gen_rat issue
prop_connection_rati08 :: Property
prop_connection_rati08 = withTests 1000 . property $ do
  x <- forAll gen_rat'
  x' <- forAll gen_rat'
  y <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int8)
  y' <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int8)

  assert $ Prop.connection (tripl rati08) x y
  assert $ Prop.connection (tripr rati08) y x
  assert $ Prop.monotonel (tripl rati08) x x'
  assert $ Prop.monotonel (tripr rati08) y y'
  assert $ Prop.monotoner (tripl rati08) y y'
  assert $ Prop.monotoner (tripr rati08) x x'
  assert $ Prop.closed (tripl rati08) x
  assert $ Prop.closed (tripr rati08) y
  assert $ Prop.kernel (tripl rati08) y
  assert $ Prop.kernel (tripr rati08) x -- x = 1 :% (-2) 

prop_connection_rati16 :: Property
prop_connection_rati16 = withTests 1000 . property $ do
  x <- forAll gen_rat'
  x' <- forAll gen_rat'
  y <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int16)
  y' <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int16)

  assert $ Prop.connection (tripl rati16) x y
  assert $ Prop.connection (tripr rati16) y x
  assert $ Prop.monotonel (tripl rati16) x x'
  assert $ Prop.monotonel (tripr rati16) y y'
  assert $ Prop.monotoner (tripl rati16) y y'
  assert $ Prop.monotoner (tripr rati16) x x'
  assert $ Prop.closed (tripl rati16) x
  assert $ Prop.closed (tripr rati16) y
  assert $ Prop.kernel (tripl rati16) y
  assert $ Prop.kernel (tripr rati16) x 

prop_connection_rati32 :: Property
prop_connection_rati32 = withTests 1000 . property $ do
  x <- forAll gen_rat'
  x' <- forAll gen_rat'
  y <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int32)
  y' <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int32)

  assert $ Prop.connection (tripl rati32) x y
  assert $ Prop.connection (tripr rati32) y x
  assert $ Prop.monotonel (tripl rati32) x x'
  assert $ Prop.monotonel (tripr rati32) y y'
  assert $ Prop.monotoner (tripl rati32) y y'
  assert $ Prop.monotoner (tripr rati32) x x'
  assert $ Prop.closed (tripl rati32) x
  assert $ Prop.closed (tripr rati32) y
  assert $ Prop.kernel (tripl rati32) y
  assert $ Prop.kernel (tripr rati32) x 

prop_connection_rati64 :: Property
prop_connection_rati64 = withTests 1000 . property $ do
  x <- forAll gen_rat'
  x' <- forAll gen_rat'
  y <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int64)
  y' <- forAll $ gen_nan $ gen_inf $ G.integral (ri @Int64)

  assert $ Prop.connection (tripl rati64) x y
  assert $ Prop.connection (tripr rati64) y x
  assert $ Prop.monotonel (tripl rati64) x x'
  assert $ Prop.monotonel (tripr rati64) y y'
  assert $ Prop.monotoner (tripl rati64) y y'
  assert $ Prop.monotoner (tripr rati64) x x'
  assert $ Prop.closed (tripl rati64) x
  assert $ Prop.closed (tripr rati64) y
  assert $ Prop.kernel (tripl rati64) y
  assert $ Prop.kernel (tripr rati64) x 

prop_connection_ratint :: Property
prop_connection_ratint = withTests 1000 . property $ do
  x <- forAll gen_rat'
  x' <- forAll gen_rat'
  y <- forAll $ gen_nan $ gen_inf $ G.integral (rint)
  y' <- forAll $ gen_nan $ gen_inf $ G.integral (rint)

  assert $ Prop.connection (tripl ratint) x y
  assert $ Prop.connection (tripr ratint) y x
  assert $ Prop.monotonel (tripl ratint) x x'
  assert $ Prop.monotonel (tripr ratint) y y'
  assert $ Prop.monotoner (tripl ratint) y y'
  assert $ Prop.monotoner (tripr ratint) x x'
  assert $ Prop.closed (tripl ratint) x
  assert $ Prop.closed (tripr ratint) y -- would fail on y = Def NaN
  assert $ Prop.kernel (tripl ratint) y
  assert $ Prop.kernel (tripr ratint) x -- x = 1 :% (-2) 

prop_connection_ratf32 :: Property
prop_connection_ratf32 = withTests 10000 . property $ do
  x <- forAll gen_rat
  x' <- forAll gen_rat
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

--tests :: IO Bool
--tests = checkParallel $$(discover)
