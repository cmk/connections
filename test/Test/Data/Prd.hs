{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Number.Tropical where

import Control.Applicative (liftA3)
import Data.Semigroup (Sum(..))
import Data.Semiring
import Data.Number.Tropical 
import Data.Number.Refined
import Hedgehog

import qualified Data.Dioid.Property as DP
import qualified Data.Semiring.Property as SP
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

rw :: Range Word
rw = R.constant 0 100

gen_min :: MonadGen m => m r -> m (Min r)
gen_min g = maybe2Min id <$> G.maybe g

gen_min_plus :: Gen (MinPlus Word)
gen_min_plus = gen_min $ Sum <$> G.word rw

prop_neutral_addition :: Property
prop_neutral_addition = property $
  assert . SP.neutral_addition zero =<< forAll gen_min_plus

prop_distributive :: Property
prop_distributive = property $ do
  a <- forAll gen_min_plus
  b <- forAll gen_min_plus
  c <- forAll gen_min_plus
  assert $ SP.distributive a b c

tests :: IO Bool
tests = checkParallel $$(discover)
