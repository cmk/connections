{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
module Test.Data.Lattice where

import Data.Connection
import Data.Lattice
import Data.Connection.Property
import Data.Lattice.Property
import Test.Data.Connection

import Hedgehog
import qualified Hedgehog.Gen as G

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

  assert $ adjointR booleanR b1 b2
  assert $ closedR booleanR b1
  assert $ kernelR booleanR b2
  assert $ monotonicR booleanR b1 b2 b3 b2
  assert $ idempotentR booleanR b1 b3

  assert $ adjointR (heyting b3) b1 b2
  assert $ closedR (heyting b3) b1
  assert $ kernelR (heyting b3) b2
  assert $ monotonicR (heyting b3) b1 b2 b3 b2
  assert $ idempotentR (heyting b3) b1 b2

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
  assert $ heytingR18 b1
  assert $ heytingR19 b1 b2
  assert $ heytingR20 b1 b2
  
  assert $ adjointR booleanR o1 o2
  assert $ closedR booleanR o1
  assert $ kernelR booleanR o2
  assert $ monotonicR booleanR o1 o2 o3 o2
  assert $ idempotentR booleanR o1 o3

  assert $ adjointR (heyting o3) o1 o2
  assert $ closedR (heyting o3) o1
  assert $ kernelR (heyting o3) o2
  assert $ monotonicR (heyting o3) o1 o2 o3 o2
  assert $ idempotentR (heyting o3) o1 o2
  
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
  assert $ heytingR18 o1
  assert $ heytingR19 o1 o2
  assert $ heytingR20 o1 o2

  assert $ adjointR booleanR w1 w2
  assert $ closedR booleanR w1
  assert $ kernelR booleanR w2
  assert $ monotonicR booleanR w1 w2 w3 w2
  assert $ idempotentR booleanR w1 w3

  assert $ adjointR (heyting w3) w1 w2
  assert $ closedR (heyting w3) w1
  assert $ kernelR (heyting w3) w2
  assert $ monotonicR (heyting w3) w1 w2 w3 w2
  assert $ idempotentR (heyting w3) w1 w2

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
  assert $ heytingR18 w1
  assert $ heytingR19 w1 w2
  assert $ heytingR20 w1 w2


 
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

  assert $ adjointL booleanL b1 b2
  assert $ closedL booleanL b1
  assert $ kernelL booleanL b2
  assert $ monotonicL booleanL b1 b2 b3 b2
  assert $ idempotentL booleanL b1 b3

  assert $ adjointL (heyting b3) b1 b2
  assert $ closedL (heyting b3) b1
  assert $ kernelL (heyting b3) b2
  assert $ monotonicL (heyting b3) b1 b2 b3 b2
  assert $ idempotentL (heyting b3) b1 b2
  
  assert $ heytingL0 b1 b2 b3
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
  
  assert $ adjointL booleanL o1 o2
  assert $ closedL booleanL o1
  assert $ kernelL booleanL o2
  assert $ monotonicL booleanL o1 o2 o3 o2
  assert $ idempotentL booleanL o1 o3

  assert $ adjointL (heyting o3) o1 o2
  assert $ closedL (heyting o3) o1
  assert $ kernelL (heyting o3) o2
  assert $ monotonicL (heyting o3) o1 o2 o3 o2
  assert $ idempotentL (heyting o3) o1 o2
  
  assert $ heytingL0 o1 o2 o3
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
  
  assert $ adjointL booleanL w1 w2
  assert $ closedL booleanL w1
  assert $ kernelL booleanL w2
  assert $ monotonicL booleanL w1 w2 w3 w2
  assert $ idempotentL booleanL w1 w3

  assert $ adjointL (heyting w3) w1 w2
  assert $ closedL (heyting w3) w1
  assert $ kernelL (heyting w3) w2
  assert $ monotonicL (heyting w3) w1 w2 w3 w2
  assert $ idempotentL (heyting w3) w1 w2

  assert $ heytingL0 w1 w2 w3
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

