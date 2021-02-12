{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
module Test.Data.Lattice where

import Data.Lattice
import Data.Connection.Property
import Data.Lattice.Property
import Test.Data.Connection

import Hedgehog
import qualified Hedgehog.Gen as G

prop_coheyting :: Property
prop_coheyting = withTests 1000 . property $ do
  b1 <- forAll G.bool
  b2 <- forAll G.bool
  b3 <- forAll G.bool
  o1 <- forAll ord
  o2 <- forAll ord
  o3 <- forAll ord
  w1 <- forAll $ G.integral (ri @Word)
  w2 <- forAll $ G.integral (ri @Word)
  w3 <- forAll $ G.integral (ri @Word)

  assert $ adjointL (algebra b3) b1 b2
  assert $ closedL (algebra b3) b1
  assert $ kernelL (algebra b3) b2
  assert $ monotonicL (algebra b3) b1 b2 b3 b2
  assert $ idempotentL (algebra b3) b1 b2

  assert $ adjointL booleanL b1 b2
  assert $ closedL booleanL b1
  assert $ kernelL booleanL b2
  assert $ monotonicL booleanL b1 b2 b3 b2
  assert $ idempotentL booleanL b1 b3
  
  assert $ coheyting1 b1 b2 b3
  assert $ coheyting2 b1 b2 b3
  assert $ coheyting3 b1 b2 b3
  assert $ coheyting4 b1 b2 b3
  assert $ coheyting5 b1 b2 b3
  assert $ coheyting6 b1 b2
  assert $ coheyting7 b1 b2
  assert $ coheyting8 b1
  assert $ coheyting9 b1 b2
  assert $ coheyting10 b1 b2
  assert $ coheyting11 b1 b2
  assert $ coheyting12 b1 b2
  assert $ coheyting13 b1 b2
  assert $ coheyting14 b1
  assert $ coheyting15 b1
  assert $ coheyting16 b1
  assert $ coheyting17 b1
  assert $ coheyting18 b1
  assert $ coheyting19 b1 b2
  assert $ coheyting20 b1 b2

  assert $ adjointL (algebra o3) o1 o2
  assert $ closedL (algebra o3) o1
  assert $ kernelL (algebra o3) o2
  assert $ monotonicL (algebra o3) o1 o2 o3 o2
  assert $ idempotentL (algebra o3) o1 o2

  assert $ adjointL booleanL o1 o2
  assert $ closedL booleanL o1
  assert $ kernelL booleanL o2
  assert $ monotonicL booleanL o1 o2 o3 o2
  assert $ idempotentL booleanL o1 o3

  assert $ coheyting1 o1 o2 o3
  assert $ coheyting2 o1 o2 o3
  assert $ coheyting3 o1 o2 o3
  assert $ coheyting4 o1 o2 o3
  assert $ coheyting5 o1 o2 o3
  assert $ coheyting6 o1 o2
  assert $ coheyting7 o1 o2
  assert $ coheyting8 o1
  assert $ coheyting9 o1 o2
  assert $ coheyting10 o1 o2
  assert $ coheyting11 o1 o2
  assert $ coheyting12 o1 o2
  assert $ coheyting13 o1 o2
  assert $ coheyting14 o1
  assert $ coheyting15 o1
  assert $ coheyting16 o1
  assert $ coheyting17 o1
  assert $ coheyting18 o1
  assert $ coheyting19 o1 o2
  assert $ coheyting20 o1 o2

  assert $ adjointL (algebra w3) w1 w2
  assert $ closedL (algebra w3) w1
  assert $ kernelL (algebra w3) w2
  assert $ monotonicL (algebra w3) w1 w2 w3 w2
  assert $ idempotentL (algebra w3) w1 w2

  assert $ adjointL booleanL w1 w2
  assert $ closedL booleanL w1
  assert $ kernelL booleanL w2
  assert $ monotonicL booleanL w1 w2 w3 w2
  assert $ idempotentL booleanL w1 w3

  assert $ coheyting1 w1 w2 w3
  assert $ coheyting2 w1 w2 w3
  assert $ coheyting3 w1 w2 w3
  assert $ coheyting4 w1 w2 w3
  assert $ coheyting5 w1 w2 w3
  assert $ coheyting6 w1 w2
  assert $ coheyting7 w1 w2
  assert $ coheyting8 w1
  assert $ coheyting9 w1 w2
  assert $ coheyting10 w1 w2
  assert $ coheyting11 w1 w2
  assert $ coheyting12 w1 w2
  assert $ coheyting13 w1 w2
  assert $ coheyting14 w1
  assert $ coheyting15 w1
  assert $ coheyting16 w1
  assert $ coheyting17 w1
  assert $ coheyting18 w1
  assert $ coheyting19 w1 w2
  assert $ coheyting20 w1 w2

prop_heyting :: Property
prop_heyting = withTests 1000 . property $ do
  b1 <- forAll G.bool
  b2 <- forAll G.bool
  b3 <- forAll G.bool
  o1 <- forAll ord
  o2 <- forAll ord
  o3 <- forAll ord
  w1 <- forAll $ G.integral (ri @Word)
  w2 <- forAll $ G.integral (ri @Word)
  w3 <- forAll $ G.integral (ri @Word)

  assert $ adjointR (algebra b3) b1 b2
  assert $ closedR (algebra b3) b1
  assert $ kernelR (algebra b3) b2
  assert $ monotonicR (algebra b3) b1 b2 b3 b2
  assert $ idempotentR (algebra b3) b1 b2
  
  assert $ adjointR booleanR b1 b2
  assert $ closedR booleanR b1
  assert $ kernelR booleanR b2
  assert $ monotonicR booleanR b1 b2 b3 b2
  assert $ idempotentR booleanR b1 b3

  assert $ heyting0 b1 b2 b3
  assert $ heyting1 b1 b2 b3
  assert $ heyting2 b1 b2 b3
  assert $ heyting3 b1 b2 b3
  assert $ heyting4 b1 b2 b3
  assert $ heyting5 b1 b2 b3
  assert $ heyting6 b1 b2
  assert $ heyting7 b1 b2
  assert $ heyting8 b1
  assert $ heyting9 b1 b2
  assert $ heyting10 b1 b2
  assert $ heyting11 b1 b2
  assert $ heyting12 b1 b2
  assert $ heyting13 b1 b2
  assert $ heyting14 b1
  assert $ heyting15 b1
  assert $ heyting16 b1
  assert $ heyting17 b1

  assert $ adjointR (algebra o3) o1 o2
  assert $ closedR (algebra o3) o1
  assert $ kernelR (algebra o3) o2
  assert $ monotonicR (algebra o3) o1 o2 o3 o2
  assert $ idempotentR (algebra o3) o1 o2

  assert $ adjointR booleanR o1 o2
  assert $ closedR booleanR o1
  assert $ kernelR booleanR o2
  assert $ monotonicR booleanR o1 o2 o3 o2
  assert $ idempotentR booleanR o1 o3

  assert $ heyting0 o1 o2 o3
  assert $ heyting1 o1 o2 o3
  assert $ heyting2 o1 o2 o3
  assert $ heyting3 o1 o2 o3
  assert $ heyting4 o1 o2 o3
  assert $ heyting5 o1 o2 o3
  assert $ heyting6 o1 o2
  assert $ heyting7 o1 o2
  assert $ heyting8 o1
  assert $ heyting9 o1 o2
  assert $ heyting10 o1 o2
  assert $ heyting11 o1 o2
  assert $ heyting12 o1 o2
  assert $ heyting13 o1 o2
  assert $ heyting14 o1
  assert $ heyting15 o1
  assert $ heyting16 o1
  assert $ heyting17 o1

  assert $ adjointR (algebra w3) w1 w2
  assert $ closedR (algebra w3) w1
  assert $ kernelR (algebra w3) w2
  assert $ monotonicR (algebra w3) w1 w2 w3 w2
  assert $ idempotentR (algebra w3) w1 w2
  
  assert $ adjointR booleanR w1 w2
  assert $ closedR booleanR w1
  assert $ kernelR booleanR w2
  assert $ monotonicR booleanR w1 w2 w3 w2
  assert $ idempotentR booleanR w1 w3

  assert $ heyting0 w1 w2 w3
  assert $ heyting1 w1 w2 w3
  assert $ heyting2 w1 w2 w3
  assert $ heyting3 w1 w2 w3
  assert $ heyting4 w1 w2 w3
  assert $ heyting5 w1 w2 w3
  assert $ heyting6 w1 w2
  assert $ heyting7 w1 w2
  assert $ heyting8 w1
  assert $ heyting9 w1 w2
  assert $ heyting10 w1 w2
  assert $ heyting11 w1 w2
  assert $ heyting12 w1 w2
  assert $ heyting13 w1 w2
  assert $ heyting14 w1
  assert $ heyting15 w1
  assert $ heyting16 w1
  assert $ heyting17 w1

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
