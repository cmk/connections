{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection.Float where

import Data.Connection.Conn
import Data.Connection.Float
import Data.Int
import Data.Fixed
import Hedgehog
import Prelude hiding (Ord(..),Bounded, until)
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Hedgehog.Gen as G

import GHC.Float
import GHC.Float.RealFracMethods 

--rationalToFloat :: Integer -> Integer -> Float

shiftf :: Integer -> Fixed a -> Fixed a
shiftf j (MkFixed i) = MkFixed (i + j)

f64f12 :: Conn k Double Pico
f64f12 = Conn f g h
  where
    f x =
        let est = double2Float x
         in if g est >~ x
                then est
                else ascend est g x
    
    g (MkFixed i) = rationalToDouble (div i $ 2^12) (2^12)

    h x =
        let est = double2Float x
         in if g est <~ x
                then est
                else descend est g x


    ascend z g1 y = until (\x -> g1 x >~ y) (<~) (shiftf 1) z

    descend z h1 x = until (\y -> h1 y <~ x) (>~) (shiftf (-1)) z

prop_connection_f32i08 :: Property
prop_connection_f32i08 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint (f32i08) x y
  assert $ Prop.closed (f32i08) x
  assert $ Prop.kernel (f32i08) y
  assert $ Prop.monotonic (f32i08) x x' y y'
  assert $ Prop.idempotent (f32i08) x y

prop_connection_f32i16 :: Property
prop_connection_f32i16 = withTests 1000 . property $ do
  x <- forAll f32
  x' <- forAll f32
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint (f32i16) x y
  assert $ Prop.closed (f32i16) x
  assert $ Prop.kernel (f32i16) y
  assert $ Prop.monotonic (f32i16) x x' y y'
  assert $ Prop.idempotent (f32i16) x y

prop_connection_f64i08 :: Property
prop_connection_f64i08 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int8)
  y' <- forAll $ gen_extended $ G.integral (ri @Int8)

  assert $ Prop.adjoint (f64i08) x y
  assert $ Prop.closed (f64i08) x
  assert $ Prop.kernel (f64i08) y
  assert $ Prop.monotonic (f64i08) x x' y y'
  assert $ Prop.idempotent (f64i08) x y

prop_connection_f64i16 :: Property
prop_connection_f64i16 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int16)
  y' <- forAll $ gen_extended $ G.integral (ri @Int16)

  assert $ Prop.adjoint (f64i16) x y
  assert $ Prop.closed (f64i16) x
  assert $ Prop.kernel (f64i16) y
  assert $ Prop.monotonic (f64i16) x x' y y'
  assert $ Prop.idempotent (f64i16) x y

prop_connection_f64i32 :: Property
prop_connection_f64i32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll $ gen_extended $ G.integral (ri @Int32)
  y' <- forAll $ gen_extended $ G.integral (ri @Int32)

  assert $ Prop.adjoint (f64i32) x y
  assert $ Prop.closed (f64i32) x
  assert $ Prop.kernel (f64i32) y
  assert $ Prop.monotonic (f64i32) x x' y y'
  assert $ Prop.idempotent (f64i32) x y

prop_connection_f64f32 :: Property
prop_connection_f64f32 = withTests 1000 . property $ do
  x <- forAll f64
  x' <- forAll f64
  y <- forAll f32
  y' <- forAll f32

  assert $ Prop.adjoint (f64f32) x y
  assert $ Prop.closed (f64f32) x
  assert $ Prop.kernel (f64f32) y
  assert $ Prop.monotonic (f64f32) x x' y y'
  assert $ Prop.idempotent (f64f32) x y

tests :: IO Bool
tests = checkParallel $$(discover)
