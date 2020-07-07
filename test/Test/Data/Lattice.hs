{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
module Test.Data.Lattice where

import Data.Connection
import Data.Lattice
import Data.Connection.Property
import Data.Lattice.Property
import Data.Order
import Test.Data.Connection

import Hedgehog
import qualified Hedgehog.Gen as G

prop_heytingL :: Property
prop_heytingL = withTests 1000 . property $ do
  b1 <- forAll G.bool
  b2 <- forAll G.bool
  b3 <- forAll G.bool
  o1 <- forAll ord
  o2 <- forAll ord
  o3 <- forAll ord
  w1 <- forAll $ G.integral (ri @Word)
  w2 <- forAll $ G.integral (ri @Word)
  w3 <- forAll $ G.integral (ri @Word)
  f1 <- forAll f32
  f2 <- forAll f32
  f3 <- forAll f32

  assert $ adjointL (heyting b3) b1 b2
  assert $ closedL (heyting b3) b1
  assert $ kernelL (heyting b3) b2
  assert $ monotonicL (heyting b3) b1 b2 b3 b2
  assert $ idempotentL (heyting b3) b1 b2

  assert $ adjointL booleanL b1 b2
  assert $ closedL booleanL b1
  assert $ kernelL booleanL b2
  assert $ monotonicL booleanL b1 b2 b3 b2
  assert $ idempotentL booleanL b1 b3
  
  assert $ heytingL1 b1 b2 b3
  assert $ heytingL2 b1 b2 b3
  assert $ heytingL3 b1 b2 b3
  assert $ heytingL4 b1 b2 b3
  assert $ heytingL5 b1 b2 b3
  assert $ heytingL6 b1 b2
  assert $ heytingL7 b1 b2
  assert $ heytingL8 b1
  assert $ heytingL9 b1 b2
  assert $ heytingL10 b1 b2
  assert $ heytingL11 b1 b2
  assert $ heytingL12 b1 b2
  assert $ heytingL13 b1 b2
  assert $ heytingL14 b1
  assert $ heytingL15 b1
  assert $ heytingL16 b1
  assert $ heytingL17 b1
  assert $ heytingL18 b1
  assert $ heytingL19 b1 b2
  assert $ heytingL20 b1 b2

  assert $ adjointL (heyting o3) o1 o2
  assert $ closedL (heyting o3) o1
  assert $ kernelL (heyting o3) o2
  assert $ monotonicL (heyting o3) o1 o2 o3 o2
  assert $ idempotentL (heyting o3) o1 o2

  assert $ adjointL booleanL o1 o2
  assert $ closedL booleanL o1
  assert $ kernelL booleanL o2
  assert $ monotonicL booleanL o1 o2 o3 o2
  assert $ idempotentL booleanL o1 o3

  assert $ heytingL1 o1 o2 o3
  assert $ heytingL2 o1 o2 o3
  assert $ heytingL3 o1 o2 o3
  assert $ heytingL4 o1 o2 o3
  assert $ heytingL5 o1 o2 o3
  assert $ heytingL6 o1 o2
  assert $ heytingL7 o1 o2
  assert $ heytingL8 o1
  assert $ heytingL9 o1 o2
  assert $ heytingL10 o1 o2
  assert $ heytingL11 o1 o2
  assert $ heytingL12 o1 o2
  assert $ heytingL13 o1 o2
  assert $ heytingL14 o1
  assert $ heytingL15 o1
  assert $ heytingL16 o1
  assert $ heytingL17 o1
  assert $ heytingL18 o1
  assert $ heytingL19 o1 o2
  assert $ heytingL20 o1 o2

  assert $ adjointL (heyting w3) w1 w2
  assert $ closedL (heyting w3) w1
  assert $ kernelL (heyting w3) w2
  assert $ monotonicL (heyting w3) w1 w2 w3 w2
  assert $ idempotentL (heyting w3) w1 w2

  assert $ adjointL booleanL w1 w2
  assert $ closedL booleanL w1
  assert $ kernelL booleanL w2
  assert $ monotonicL booleanL w1 w2 w3 w2
  assert $ idempotentL booleanL w1 w3

  assert $ heytingL1 w1 w2 w3
  assert $ heytingL2 w1 w2 w3
  assert $ heytingL3 w1 w2 w3
  assert $ heytingL4 w1 w2 w3
  assert $ heytingL5 w1 w2 w3
  assert $ heytingL6 w1 w2
  assert $ heytingL7 w1 w2
  assert $ heytingL8 w1
  assert $ heytingL9 w1 w2
  assert $ heytingL10 w1 w2
  assert $ heytingL11 w1 w2
  assert $ heytingL12 w1 w2
  assert $ heytingL13 w1 w2
  assert $ heytingL14 w1
  assert $ heytingL15 w1
  assert $ heytingL16 w1
  assert $ heytingL17 w1
  assert $ heytingL18 w1
  assert $ heytingL19 w1 w2
  assert $ heytingL20 w1 w2

prop_heytingR :: Property
prop_heytingR = withTests 1000 . property $ do
  b1 <- forAll G.bool
  b2 <- forAll G.bool
  b3 <- forAll G.bool
  o1 <- forAll ord
  o2 <- forAll ord
  o3 <- forAll ord
  w1 <- forAll $ G.integral (ri @Word)
  w2 <- forAll $ G.integral (ri @Word)
  w3 <- forAll $ G.integral (ri @Word)

  assert $ adjointR (heyting b3) b1 b2
  assert $ closedR (heyting b3) b1
  assert $ kernelR (heyting b3) b2
  assert $ monotonicR (heyting b3) b1 b2 b3 b2
  assert $ idempotentR (heyting b3) b1 b2
  
  assert $ adjointR booleanR b1 b2
  assert $ closedR booleanR b1
  assert $ kernelR booleanR b2
  assert $ monotonicR booleanR b1 b2 b3 b2
  assert $ idempotentR booleanR b1 b3

  assert $ heytingR0 b1 b2 b3
  assert $ heytingR1 b1 b2 b3
  assert $ heytingR2 b1 b2 b3
  assert $ heytingR3 b1 b2 b3
  assert $ heytingR4 b1 b2 b3
  assert $ heytingR5 b1 b2 b3
  assert $ heytingR6 b1 b2
  assert $ heytingR7 b1 b2
  assert $ heytingR8 b1
  assert $ heytingR9 b1 b2
  assert $ heytingR10 b1 b2
  assert $ heytingR11 b1 b2
  assert $ heytingR12 b1 b2
  assert $ heytingR13 b1 b2
  assert $ heytingR14 b1
  assert $ heytingR15 b1
  assert $ heytingR16 b1
  assert $ heytingR17 b1

  assert $ adjointR (heyting o3) o1 o2
  assert $ closedR (heyting o3) o1
  assert $ kernelR (heyting o3) o2
  assert $ monotonicR (heyting o3) o1 o2 o3 o2
  assert $ idempotentR (heyting o3) o1 o2

  assert $ adjointR booleanR o1 o2
  assert $ closedR booleanR o1
  assert $ kernelR booleanR o2
  assert $ monotonicR booleanR o1 o2 o3 o2
  assert $ idempotentR booleanR o1 o3

  assert $ heytingR0 o1 o2 o3
  assert $ heytingR1 o1 o2 o3
  assert $ heytingR2 o1 o2 o3
  assert $ heytingR3 o1 o2 o3
  assert $ heytingR4 o1 o2 o3
  assert $ heytingR5 o1 o2 o3
  assert $ heytingR6 o1 o2
  assert $ heytingR7 o1 o2
  assert $ heytingR8 o1
  assert $ heytingR9 o1 o2
  assert $ heytingR10 o1 o2
  assert $ heytingR11 o1 o2
  assert $ heytingR12 o1 o2
  assert $ heytingR13 o1 o2
  assert $ heytingR14 o1
  assert $ heytingR15 o1
  assert $ heytingR16 o1
  assert $ heytingR17 o1

  assert $ adjointR (heyting w3) w1 w2
  assert $ closedR (heyting w3) w1
  assert $ kernelR (heyting w3) w2
  assert $ monotonicR (heyting w3) w1 w2 w3 w2
  assert $ idempotentR (heyting w3) w1 w2
  
  assert $ adjointR booleanR w1 w2
  assert $ closedR booleanR w1
  assert $ kernelR booleanR w2
  assert $ monotonicR booleanR w1 w2 w3 w2
  assert $ idempotentR booleanR w1 w3

  assert $ heytingR0 w1 w2 w3
  assert $ heytingR1 w1 w2 w3
  assert $ heytingR2 w1 w2 w3
  assert $ heytingR3 w1 w2 w3
  assert $ heytingR4 w1 w2 w3
  assert $ heytingR5 w1 w2 w3
  assert $ heytingR6 w1 w2
  assert $ heytingR7 w1 w2
  assert $ heytingR8 w1
  assert $ heytingR9 w1 w2
  assert $ heytingR10 w1 w2
  assert $ heytingR11 w1 w2
  assert $ heytingR12 w1 w2
  assert $ heytingR13 w1 w2
  assert $ heytingR14 w1
  assert $ heytingR15 w1
  assert $ heytingR16 w1
  assert $ heytingR17 w1

prop_symmetric :: Property
prop_symmetric = withTests 1000 . property $ do
  b1 <- forAll G.bool
  b2 <- forAll G.bool
  b3 <- forAll G.bool
  o1 <- forAll ord
  o2 <- forAll ord
 
  assert $ symmetric1 b1
  assert $ symmetric2 b1
  assert $ symmetric3 b1
  assert $ symmetric4 b1
  assert $ symmetric5 b1
  assert $ symmetric6 b1
  assert $ symmetric7 b1 b2
  assert $ symmetric8 b1 b2
  assert $ symmetric9 b1 b2
  assert $ symmetric10 b1 b2
  assert $ symmetric11 b1 b2
  assert $ symmetric12 b1 b2
  assert $ symmetric13 b1 b2
 
  assert $ adjoint boolean b1 b2
  assert $ closed boolean b1
  assert $ kernel boolean b2
  assert $ monotonic boolean b1 b2 b3 b2
  assert $ idempotent boolean b1 b3

  assert $ boolean0 b1
  assert $ boolean1 b1
  assert $ boolean2 b1
  assert $ boolean3 b1
  assert $ boolean4 b1 b2
  assert $ boolean5 b1 b2
  assert $ boolean6 b1 b2
  
  assert $ symmetric1 o1
  assert $ symmetric2 o1
  assert $ symmetric3 o1
  assert $ symmetric4 o1
  assert $ symmetric5 o1
  assert $ symmetric6 o1
  assert $ symmetric7 o1 o2
  assert $ symmetric8 o1 o2
  assert $ symmetric9 o1 o2
  assert $ symmetric10 o1 o2
  assert $ symmetric11 o1 o2
  assert $ symmetric12 o1 o2
  assert $ symmetric13 o1 o2

tests :: IO Bool
tests = checkParallel $$(discover)
