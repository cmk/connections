{-# LANGUAGE TemplateHaskell #-}
{-# Language AllowAmbiguousTypes #-}
module Test.Data.Connection.Ratio where

import Data.Int
import Data.Word
import Data.Connection.Type
import Data.Connection.Ratio
import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G


prop_connection_ratf32 :: Property
prop_connection_ratf32 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll f32
  y' <- forAll f32

  assert $ Prop.adjoint (tripr ratf32) x y
  assert $ Prop.adjoint (tripl ratf32) y x
  assert $ Prop.closed (tripr ratf32) x
  assert $ Prop.closed (tripl ratf32) y
  assert $ Prop.kernel (tripr ratf32) y
  assert $ Prop.kernel (tripl ratf32) x
  assert $ Prop.monotoneR (tripr ratf32) y y'
  assert $ Prop.monotoneR (tripl ratf32) x x'
  assert $ Prop.monotoneL (tripr ratf32) x x'
  assert $ Prop.monotoneL (tripl ratf32) y y'
  assert $ Prop.projectiveL (tripr ratf32) x
  assert $ Prop.projectiveL (tripl ratf32) y
  assert $ Prop.projectiveR (tripr ratf32) y
  assert $ Prop.projectiveR (tripl ratf32) x

prop_connection_ratf64 :: Property
prop_connection_ratf64 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll f64
  y' <- forAll f64

  assert $ Prop.adjoint (tripr ratf64) x y
  assert $ Prop.adjoint (tripl ratf64) y x
  assert $ Prop.closed (tripr ratf64) x
  assert $ Prop.closed (tripl ratf64) y
  assert $ Prop.kernel (tripr ratf64) y
  assert $ Prop.kernel (tripl ratf64) x
  assert $ Prop.monotoneR (tripr ratf64) y y'
  assert $ Prop.monotoneR (tripl ratf64) x x'
  assert $ Prop.monotoneL (tripr ratf64) x x'
  assert $ Prop.monotoneL (tripl ratf64) y y'
  assert $ Prop.projectiveL (tripr ratf64) x
  assert $ Prop.projectiveL (tripl ratf64) y
  assert $ Prop.projectiveR (tripr ratf64) y
  assert $ Prop.projectiveR (tripl ratf64) x

prop_connection_rati08 :: Property
prop_connection_rati08 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll . gen_extended $ G.integral (ri @Int8)
  y' <- forAll . gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint (tripr rati08) x y
  assert $ Prop.adjoint (tripl rati08) y x
  assert $ Prop.closed (tripr rati08) x
  assert $ Prop.closed (tripl rati08) y
  assert $ Prop.kernel (tripr rati08) y
  assert $ Prop.kernel (tripl rati08) x
  assert $ Prop.monotoneL (tripr rati08) x x'
  assert $ Prop.monotoneL (tripl rati08) y y'
  assert $ Prop.monotoneR (tripr rati08) y y'
  assert $ Prop.monotoneR (tripl rati08) x x'
  assert $ Prop.projectiveL (tripr rati08) x
  assert $ Prop.projectiveL (tripl rati08) y
  assert $ Prop.projectiveR (tripr rati08) y
  assert $ Prop.projectiveR (tripl rati08) x

prop_connection_rati16 :: Property
prop_connection_rati16 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll . gen_extended $ G.integral (ri @Int16)
  y' <- forAll . gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint (tripr rati16) x y
  assert $ Prop.adjoint (tripl rati16) y x
  assert $ Prop.closed (tripr rati16) x
  assert $ Prop.closed (tripl rati16) y
  assert $ Prop.kernel (tripr rati16) y
  assert $ Prop.kernel (tripl rati16) x 
  assert $ Prop.monotoneL (tripr rati16) x x'
  assert $ Prop.monotoneL (tripl rati16) y y'
  assert $ Prop.monotoneR (tripr rati16) y y'
  assert $ Prop.monotoneR (tripl rati16) x x'
  assert $ Prop.projectiveL (tripr rati16) x
  assert $ Prop.projectiveL (tripl rati16) y
  assert $ Prop.projectiveR (tripr rati16) y
  assert $ Prop.projectiveR (tripl rati16) x

prop_connection_rati32 :: Property
prop_connection_rati32 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll . gen_extended $ G.integral (ri @Int32)
  y' <- forAll . gen_extended $ G.integral (ri @Int32)

  assert $ Prop.adjoint (tripr rati32) x y
  assert $ Prop.adjoint (tripl rati32) y x
  assert $ Prop.closed (tripr rati32) x
  assert $ Prop.closed (tripl rati32) y
  assert $ Prop.kernel (tripr rati32) y
  assert $ Prop.kernel (tripl rati32) x 
  assert $ Prop.monotoneL (tripr rati32) x x'
  assert $ Prop.monotoneL (tripl rati32) y y'
  assert $ Prop.monotoneR (tripr rati32) y y'
  assert $ Prop.monotoneR (tripl rati32) x x'
  assert $ Prop.projectiveL (tripr rati32) x
  assert $ Prop.projectiveL (tripl rati32) y
  assert $ Prop.projectiveR (tripr rati32) y
  assert $ Prop.projectiveR (tripl rati32) x

prop_connection_rati64 :: Property
prop_connection_rati64 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll . gen_extended $ G.integral (ri @Int64)
  y' <- forAll . gen_extended $ G.integral (ri @Int64)

  assert $ Prop.adjoint (tripr rati64) x y
  assert $ Prop.adjoint (tripl rati64) y x
  assert $ Prop.closed (tripr rati64) x
  assert $ Prop.closed (tripl rati64) y
  assert $ Prop.kernel (tripr rati64) y
  assert $ Prop.kernel (tripl rati64) x 
  assert $ Prop.monotoneL (tripr rati64) x x'
  assert $ Prop.monotoneL (tripl rati64) y y'
  assert $ Prop.monotoneR (tripr rati64) y y'
  assert $ Prop.monotoneR (tripl rati64) x x'
  assert $ Prop.projectiveL (tripr rati64) x
  assert $ Prop.projectiveL (tripl rati64) y
  assert $ Prop.projectiveR (tripr rati64) y
  assert $ Prop.projectiveR (tripl rati64) x

prop_connection_ratint :: Property
prop_connection_ratint = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll . gen_extended $ G.integral ri'
  y' <- forAll . gen_extended $ G.integral ri'

  assert $ Prop.adjoint (tripr ratint) x y
  assert $ Prop.adjoint (tripl ratint) y x
  assert $ Prop.closed (tripr ratint) x
  assert $ Prop.closed (tripl ratint) y
  assert $ Prop.kernel (tripr ratint) y
  assert $ Prop.kernel (tripl ratint) x
  assert $ Prop.monotoneL (tripr ratint) x x'
  assert $ Prop.monotoneL (tripl ratint) y y'
  assert $ Prop.monotoneR (tripr ratint) y y'
  assert $ Prop.monotoneR (tripl ratint) x x'
  assert $ Prop.projectiveL (tripr ratint) x
  assert $ Prop.projectiveL (tripl ratint) y
  assert $ Prop.projectiveR (tripr ratint) y
  assert $ Prop.projectiveR (tripl ratint) x

prop_connection_ratw08 :: Property
prop_connection_ratw08 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll . gen_lowered $ G.integral (ri @Word8)
  y' <- forAll . gen_lowered $ G.integral (ri @Word8)

  assert $ Prop.adjoint (tripr ratw08) x y
  assert $ Prop.adjoint (tripl ratw08) y x
  assert $ Prop.closed (tripr ratw08) x
  assert $ Prop.closed (tripl ratw08) y
  assert $ Prop.kernel (tripr ratw08) y
  assert $ Prop.kernel (tripl ratw08) x 
  assert $ Prop.monotoneL (tripr ratw08) x x'
  assert $ Prop.monotoneL (tripl ratw08) y y'
  assert $ Prop.monotoneR (tripr ratw08) y y'
  assert $ Prop.monotoneR (tripl ratw08) x x'
  assert $ Prop.projectiveL (tripr ratw08) x
  assert $ Prop.projectiveL (tripl ratw08) y
  assert $ Prop.projectiveR (tripr ratw08) y
  assert $ Prop.projectiveR (tripl ratw08) x

prop_connection_ratw16 :: Property
prop_connection_ratw16 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll . gen_lowered $ G.integral (ri @Word16)
  y' <- forAll . gen_lowered $ G.integral (ri @Word16)

  assert $ Prop.adjoint (tripr ratw16) x y
  assert $ Prop.adjoint (tripl ratw16) y x
  assert $ Prop.closed (tripr ratw16) x
  assert $ Prop.closed (tripl ratw16) y
  assert $ Prop.kernel (tripr ratw16) y
  assert $ Prop.kernel (tripl ratw16) x 
  assert $ Prop.monotoneL (tripr ratw16) x x'
  assert $ Prop.monotoneL (tripl ratw16) y y'
  assert $ Prop.monotoneR (tripr ratw16) y y'
  assert $ Prop.monotoneR (tripl ratw16) x x'
  assert $ Prop.projectiveL (tripr ratw16) x
  assert $ Prop.projectiveL (tripl ratw16) y
  assert $ Prop.projectiveR (tripr ratw16) y
  assert $ Prop.projectiveR (tripl ratw16) x

prop_connection_ratw32 :: Property
prop_connection_ratw32 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll . gen_lowered $ G.integral (ri @Word32)
  y' <- forAll . gen_lowered $ G.integral (ri @Word32)

  assert $ Prop.adjoint (tripr ratw32) x y
  assert $ Prop.adjoint (tripl ratw32) y x
  assert $ Prop.closed (tripr ratw32) x
  assert $ Prop.closed (tripl ratw32) y
  assert $ Prop.kernel (tripr ratw32) y
  assert $ Prop.kernel (tripl ratw32) x 
  assert $ Prop.monotoneL (tripr ratw32) x x'
  assert $ Prop.monotoneL (tripl ratw32) y y'
  assert $ Prop.monotoneR (tripr ratw32) y y'
  assert $ Prop.monotoneR (tripl ratw32) x x'
  assert $ Prop.projectiveL (tripr ratw32) x
  assert $ Prop.projectiveL (tripl ratw32) y
  assert $ Prop.projectiveR (tripr ratw32) y
  assert $ Prop.projectiveR (tripl ratw32) x

prop_connection_ratw64 :: Property
prop_connection_ratw64 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll . gen_lowered $ G.integral (ri @Word64)
  y' <- forAll . gen_lowered $ G.integral (ri @Word64)

  assert $ Prop.adjoint (tripr ratw64) x y
  assert $ Prop.adjoint (tripl ratw64) y x
  assert $ Prop.closed (tripr ratw64) x
  assert $ Prop.closed (tripl ratw64) y
  assert $ Prop.kernel (tripr ratw64) y
  assert $ Prop.kernel (tripl ratw64) x 
  assert $ Prop.monotoneL (tripr ratw64) x x'
  assert $ Prop.monotoneL (tripl ratw64) y y'
  assert $ Prop.monotoneR (tripr ratw64) y y'
  assert $ Prop.monotoneR (tripl ratw64) x x'
  assert $ Prop.projectiveL (tripr ratw64) x
  assert $ Prop.projectiveL (tripl ratw64) y
  assert $ Prop.projectiveR (tripr ratw64) y
  assert $ Prop.projectiveR (tripl ratw64) x

prop_connection_ratnat :: Property
prop_connection_ratnat = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll . gen_lowered $ G.integral rn
  y' <- forAll . gen_lowered $ G.integral rn

  assert $ Prop.adjoint (tripr ratnat) x y
  assert $ Prop.adjoint (tripl ratnat) y x
  assert $ Prop.closed (tripr ratnat) x
  assert $ Prop.closed (tripl ratnat) y
  assert $ Prop.kernel (tripr ratnat) y
  assert $ Prop.kernel (tripl ratnat) x
  assert $ Prop.monotoneL (tripr ratnat) x x'
  assert $ Prop.monotoneL (tripl ratnat) y y'
  assert $ Prop.monotoneR (tripr ratnat) y y'
  assert $ Prop.monotoneR (tripl ratnat) x x'
  assert $ Prop.projectiveL (tripr ratnat) x
  assert $ Prop.projectiveL (tripl ratnat) y
  assert $ Prop.projectiveR (tripr ratnat) y
  assert $ Prop.projectiveR (tripl ratnat) x

tests :: IO Bool
tests = checkParallel $$(discover)
