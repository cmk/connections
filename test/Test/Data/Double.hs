{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Double where

import Data.Connection
--import Data.Double

import qualified Data.Connection.Property as Prop

import Hedgehog
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R


rd :: Range Double
rd = R.exponentialFloatFrom 0 (-1.7976931348623157e308) 1.7976931348623157e308

ri :: Range Int
ri = R.exponentialFrom 0 minBound maxBound

gen_ex :: RealFloat a => Gen a
gen_ex = G.element [(-1)/0, 1/0, 0/0]

gen_double :: Gen Double
gen_double = G.frequency [(9, G.double rd), (1, gen_ex)] 

{-
prop_closed_f32i64 :: Property
prop_closed_f32i64 = property $
  assert . Prop.closed f32i64 =<< forAll gen_float

prop_closed_i64f32 :: Property
prop_closed_i64f32 = property $
  assert . Prop.closed i64f32 =<< forAll (G.maybe . G.integral $ ri)

prop_kernel_f32i64 :: Property
prop_kernel_f32i64 = property $
  assert . Prop.kernel f32i64 =<< forAll (G.maybe . G.integral $ ri)

prop_kernel_i64f32 :: Property
prop_kernel_i64f32 = property $
  assert . Prop.kernel i64f32 =<< forAll gen_float
-}

prop_closed_double_int :: Property
prop_closed_double_int = property $
  assert . Prop.closed double_int =<< forAll gen_double

prop_closed_int_double :: Property
prop_closed_int_double = property $
  assert . Prop.closed int_double =<< forAll (G.maybe . G.integral $ ri)

prop_kernel_double_int :: Property
prop_kernel_double_int = property $
  assert . Prop.kernel double_int =<< forAll (G.maybe . G.integral $ ri)

prop_kernel_int_double :: Property
prop_kernel_int_double = property $
  assert . Prop.kernel int_double =<< forAll gen_double

tests :: IO Bool
tests = checkParallel $$(discover)
