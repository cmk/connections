{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Float.Unit where

import Control.Applicative
import Data.Connection
import Data.Float
import Data.Float.Unit hiding (bnt, unt)
import Data.Prd
import Data.Ratio
import Data.Semifield
import Data.Semilattice.N5
import Data.Semilattice.Top
import Data.Word
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Hedgehog
import Numeric.Natural
import Prelude hiding (Bounded)
import Test.Data.Connection
import qualified Data.Connection.Property as Prop
import qualified Data.Prd.Property as Prop
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

prop_connection_untf64 :: Property
prop_connection_untf64 = withTests 1000 . property $ do
  x <- forAll $ gen_bot unt
  x' <- forAll $ gen_bot unt
  y <- forAll $ gen_pn5 f64
  y' <- forAll $ gen_pn5 f64

  assert $ Prop.connection untf64 x y
  assert $ Prop.closed untf64 x
  assert $ Prop.kernel untf64 y
  assert $ Prop.monotonel untf64 x x'
  assert $ Prop.monotoner untf64 y y'
  assert $ Prop.projectivel untf64 x
  assert $ Prop.projectiver untf64 y

prop_connection_bntf64 :: Property
prop_connection_bntf64 = withTests 1000 . property $ do
  x <- forAll $ gen_bot bnt
  x' <- forAll $ gen_bot bnt
  y <- forAll $ gen_pn5 f64
  y' <- forAll $ gen_pn5 f64

  assert $ Prop.connection bntf64 x y
  assert $ Prop.closed bntf64 x
  assert $ Prop.kernel bntf64 y
  assert $ Prop.monotonel bntf64 x x'
  assert $ Prop.monotoner bntf64 y y'
  assert $ Prop.projectivel bntf64 x
  assert $ Prop.projectiver bntf64 y

tests :: IO Bool
tests = checkParallel $$(discover)
