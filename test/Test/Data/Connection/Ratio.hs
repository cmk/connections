{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Ratio where

import Data.Connection.Conn
import Data.Connection.Trip
import Data.Connection.Ratio
import Data.Int
import Data.Prd.Nan
import Data.Word
import Hedgehog
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

prop_connection_ratord :: Property
prop_connection_ratord = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_nan ord
  y' <- forAll $ gen_nan ord

  assert $ Prop.adjoined (tripl ratord) x y
  assert $ Prop.adjoined (tripr ratord) y x
  assert $ Prop.closed (tripl ratord) x
  assert $ Prop.closed (tripr ratord) y
  assert $ Prop.kernel (tripl ratord) y
  assert $ Prop.kernel (tripr ratord) x
  assert $ Prop.monotonel (tripl ratord) x x'
  assert $ Prop.monotonel (tripr ratord) y y'
  assert $ Prop.monotoner (tripl ratord) y y'
  assert $ Prop.monotoner (tripr ratord) x x'
  assert $ Prop.projectivel (tripl ratord) x
  assert $ Prop.projectivel (tripr ratord) y
  assert $ Prop.projectiver (tripl ratord) y
  assert $ Prop.projectiver (tripr ratord) x

prop_connection_ratf32 :: Property
prop_connection_ratf32 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll f32
  y' <- forAll f32

  assert $ Prop.adjoined (tripl ratf32) x y
  assert $ Prop.adjoined (tripr ratf32) y x
  assert $ Prop.closed (tripl ratf32) x
  assert $ Prop.closed (tripr ratf32) y
  assert $ Prop.kernel (tripl ratf32) y
  assert $ Prop.kernel (tripr ratf32) x
  assert $ Prop.monotoner (tripl ratf32) y y'
  assert $ Prop.monotoner (tripr ratf32) x x'
  assert $ Prop.monotonel (tripl ratf32) x x'
  assert $ Prop.monotonel (tripr ratf32) y y'
  assert $ Prop.projectivel (tripl ratf32) x
  assert $ Prop.projectivel (tripr ratf32) y
  assert $ Prop.projectiver (tripl ratf32) y
  assert $ Prop.projectiver (tripr ratf32) x

prop_connection_ratf64 :: Property
prop_connection_ratf64 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll f64
  y' <- forAll f64

  assert $ Prop.adjoined (tripl ratf64) x y
  assert $ Prop.adjoined (tripr ratf64) y x
  assert $ Prop.closed (tripl ratf64) x
  assert $ Prop.closed (tripr ratf64) y
  assert $ Prop.kernel (tripl ratf64) y
  assert $ Prop.kernel (tripr ratf64) x
  assert $ Prop.monotoner (tripl ratf64) y y'
  assert $ Prop.monotoner (tripr ratf64) x x'
  assert $ Prop.monotonel (tripl ratf64) x x'
  assert $ Prop.monotonel (tripr ratf64) y y'
  assert $ Prop.projectivel (tripl ratf64) x
  assert $ Prop.projectivel (tripr ratf64) y
  assert $ Prop.projectiver (tripl ratf64) y
  assert $ Prop.projectiver (tripr ratf64) x

prop_connection_rati08 :: Property
prop_connection_rati08 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_ext $ G.integral (ri @Int8)
  y' <- forAll $ gen_ext $ G.integral (ri @Int8)

  assert $ Prop.adjoined (tripl rati08) x y
  assert $ Prop.adjoined (tripr rati08) y x
  assert $ Prop.closed (tripl rati08) x
  assert $ Prop.closed (tripr rati08) y
  assert $ Prop.kernel (tripl rati08) y
  assert $ Prop.kernel (tripr rati08) x
  assert $ Prop.monotonel (tripl rati08) x x'
  assert $ Prop.monotonel (tripr rati08) y y'
  assert $ Prop.monotoner (tripl rati08) y y'
  assert $ Prop.monotoner (tripr rati08) x x'
  assert $ Prop.projectivel (tripl rati08) x
  assert $ Prop.projectivel (tripr rati08) y
  assert $ Prop.projectiver (tripl rati08) y
  assert $ Prop.projectiver (tripr rati08) x

prop_connection_rati16 :: Property
prop_connection_rati16 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_ext $ G.integral (ri @Int16)
  y' <- forAll $ gen_ext $ G.integral (ri @Int16)

  assert $ Prop.adjoined (tripl rati16) x y
  assert $ Prop.adjoined (tripr rati16) y x
  assert $ Prop.closed (tripl rati16) x
  assert $ Prop.closed (tripr rati16) y
  assert $ Prop.kernel (tripl rati16) y
  assert $ Prop.kernel (tripr rati16) x 
  assert $ Prop.monotonel (tripl rati16) x x'
  assert $ Prop.monotonel (tripr rati16) y y'
  assert $ Prop.monotoner (tripl rati16) y y'
  assert $ Prop.monotoner (tripr rati16) x x'
  assert $ Prop.projectivel (tripl rati16) x
  assert $ Prop.projectivel (tripr rati16) y
  assert $ Prop.projectiver (tripl rati16) y
  assert $ Prop.projectiver (tripr rati16) x

prop_connection_rati32 :: Property
prop_connection_rati32 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_ext $ G.integral (ri @Int32)
  y' <- forAll $ gen_ext $ G.integral (ri @Int32)

  assert $ Prop.adjoined (tripl rati32) x y
  assert $ Prop.adjoined (tripr rati32) y x
  assert $ Prop.closed (tripl rati32) x
  assert $ Prop.closed (tripr rati32) y
  assert $ Prop.kernel (tripl rati32) y
  assert $ Prop.kernel (tripr rati32) x 
  assert $ Prop.monotonel (tripl rati32) x x'
  assert $ Prop.monotonel (tripr rati32) y y'
  assert $ Prop.monotoner (tripl rati32) y y'
  assert $ Prop.monotoner (tripr rati32) x x'
  assert $ Prop.projectivel (tripl rati32) x
  assert $ Prop.projectivel (tripr rati32) y
  assert $ Prop.projectiver (tripl rati32) y
  assert $ Prop.projectiver (tripr rati32) x

prop_connection_rati64 :: Property
prop_connection_rati64 = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_ext $ G.integral (ri @Int64)
  y' <- forAll $ gen_ext $ G.integral (ri @Int64)

  assert $ Prop.adjoined (tripl rati64) x y
  assert $ Prop.adjoined (tripr rati64) y x
  assert $ Prop.closed (tripl rati64) x
  assert $ Prop.closed (tripr rati64) y
  assert $ Prop.kernel (tripl rati64) y
  assert $ Prop.kernel (tripr rati64) x 
  assert $ Prop.monotonel (tripl rati64) x x'
  assert $ Prop.monotonel (tripr rati64) y y'
  assert $ Prop.monotoner (tripl rati64) y y'
  assert $ Prop.monotoner (tripr rati64) x x'
  assert $ Prop.projectivel (tripl rati64) x
  assert $ Prop.projectivel (tripr rati64) y
  assert $ Prop.projectiver (tripl rati64) y
  assert $ Prop.projectiver (tripr rati64) x

prop_connection_ratint :: Property
prop_connection_ratint = withTests 1000 . property $ do
  x <- forAll rat
  x' <- forAll rat
  y <- forAll $ gen_ext $ G.integral ri'
  y' <- forAll $ gen_ext $ G.integral ri'

  assert $ Prop.adjoined (tripl ratint) x y
  assert $ Prop.adjoined (tripr ratint) y x
  assert $ Prop.closed (tripl ratint) x
  assert $ Prop.closed (tripr ratint) y
  assert $ Prop.kernel (tripl ratint) y
  assert $ Prop.kernel (tripr ratint) x
  assert $ Prop.monotonel (tripl ratint) x x'
  assert $ Prop.monotonel (tripr ratint) y y'
  assert $ Prop.monotoner (tripl ratint) y y'
  assert $ Prop.monotoner (tripr ratint) x x'
  assert $ Prop.projectivel (tripl ratint) x
  assert $ Prop.projectivel (tripr ratint) y
  assert $ Prop.projectiver (tripl ratint) y
  assert $ Prop.projectiver (tripr ratint) x

prop_connection_ratw08 :: Property
prop_connection_ratw08 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll $ gen_lft $ G.integral (ri @Word8)
  y' <- forAll $ gen_lft $ G.integral (ri @Word8)

  assert $ Prop.adjoined (tripl ratw08) x y
  assert $ Prop.adjoined (tripr ratw08) y x
  assert $ Prop.closed (tripl ratw08) x
  assert $ Prop.closed (tripr ratw08) y
  assert $ Prop.kernel (tripl ratw08) y
  assert $ Prop.kernel (tripr ratw08) x 
  assert $ Prop.monotonel (tripl ratw08) x x'
  assert $ Prop.monotonel (tripr ratw08) y y'
  assert $ Prop.monotoner (tripl ratw08) y y'
  assert $ Prop.monotoner (tripr ratw08) x x'
  assert $ Prop.projectivel (tripl ratw08) x
  assert $ Prop.projectivel (tripr ratw08) y
  assert $ Prop.projectiver (tripl ratw08) y
  assert $ Prop.projectiver (tripr ratw08) x

prop_connection_ratw16 :: Property
prop_connection_ratw16 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll $ gen_lft $ G.integral (ri @Word16)
  y' <- forAll $ gen_lft $ G.integral (ri @Word16)

  assert $ Prop.adjoined (tripl ratw16) x y
  assert $ Prop.adjoined (tripr ratw16) y x
  assert $ Prop.closed (tripl ratw16) x
  assert $ Prop.closed (tripr ratw16) y
  assert $ Prop.kernel (tripl ratw16) y
  assert $ Prop.kernel (tripr ratw16) x 
  assert $ Prop.monotonel (tripl ratw16) x x'
  assert $ Prop.monotonel (tripr ratw16) y y'
  assert $ Prop.monotoner (tripl ratw16) y y'
  assert $ Prop.monotoner (tripr ratw16) x x'
  assert $ Prop.projectivel (tripl ratw16) x
  assert $ Prop.projectivel (tripr ratw16) y
  assert $ Prop.projectiver (tripl ratw16) y
  assert $ Prop.projectiver (tripr ratw16) x

prop_connection_ratw32 :: Property
prop_connection_ratw32 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll $ gen_lft $ G.integral (ri @Word32)
  y' <- forAll $ gen_lft $ G.integral (ri @Word32)

  assert $ Prop.adjoined (tripl ratw32) x y
  assert $ Prop.adjoined (tripr ratw32) y x
  assert $ Prop.closed (tripl ratw32) x
  assert $ Prop.closed (tripr ratw32) y
  assert $ Prop.kernel (tripl ratw32) y
  assert $ Prop.kernel (tripr ratw32) x 
  assert $ Prop.monotonel (tripl ratw32) x x'
  assert $ Prop.monotonel (tripr ratw32) y y'
  assert $ Prop.monotoner (tripl ratw32) y y'
  assert $ Prop.monotoner (tripr ratw32) x x'
  assert $ Prop.projectivel (tripl ratw32) x
  assert $ Prop.projectivel (tripr ratw32) y
  assert $ Prop.projectiver (tripl ratw32) y
  assert $ Prop.projectiver (tripr ratw32) x

prop_connection_ratw64 :: Property
prop_connection_ratw64 = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll $ gen_lft $ G.integral (ri @Word64)
  y' <- forAll $ gen_lft $ G.integral (ri @Word64)

  assert $ Prop.adjoined (tripl ratw64) x y
  assert $ Prop.adjoined (tripr ratw64) y x
  assert $ Prop.closed (tripl ratw64) x
  assert $ Prop.closed (tripr ratw64) y
  assert $ Prop.kernel (tripl ratw64) y
  assert $ Prop.kernel (tripr ratw64) x 
  assert $ Prop.monotonel (tripl ratw64) x x'
  assert $ Prop.monotonel (tripr ratw64) y y'
  assert $ Prop.monotoner (tripl ratw64) y y'
  assert $ Prop.monotoner (tripr ratw64) x x'
  assert $ Prop.projectivel (tripl ratw64) x
  assert $ Prop.projectivel (tripr ratw64) y
  assert $ Prop.projectiver (tripl ratw64) y
  assert $ Prop.projectiver (tripr ratw64) x

prop_connection_ratnat :: Property
prop_connection_ratnat = withTests 1000 . property $ do
  x <- forAll pos
  x' <- forAll pos
  y <- forAll $ gen_lft $ G.integral rn
  y' <- forAll $ gen_lft $ G.integral rn

  assert $ Prop.adjoined (tripl ratnat) x y
  assert $ Prop.adjoined (tripr ratnat) y x
  assert $ Prop.closed (tripl ratnat) x
  assert $ Prop.closed (tripr ratnat) y
  assert $ Prop.kernel (tripl ratnat) y
  assert $ Prop.kernel (tripr ratnat) x
  assert $ Prop.monotonel (tripl ratnat) x x'
  assert $ Prop.monotonel (tripr ratnat) y y'
  assert $ Prop.monotoner (tripl ratnat) y y'
  assert $ Prop.monotoner (tripr ratnat) x x'
  assert $ Prop.projectivel (tripl ratnat) x
  assert $ Prop.projectivel (tripr ratnat) y
  assert $ Prop.projectiver (tripl ratnat) y
  assert $ Prop.projectiver (tripr ratnat) x

tests :: IO Bool
tests = checkParallel $$(discover)
