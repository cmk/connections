{-# LANGUAGE TemplateHaskell #-}
module Test.Data.Connection where

import Control.Applicative
import Data.Connection.Type
import Data.Connection.Ratio
import Data.Lattice
import Data.Ord
import Data.Order.Extended
import GHC.Real hiding (Fractional(..), (^^), (^), div)
import Hedgehog
import Numeric.Natural
import Prelude hiding (Bounded)
import qualified Hedgehog.Gen as G
import qualified Hedgehog.Range as R

ri :: (Integral a, Bounded a) => Range a
ri = R.linearFrom 0 bottom top

ri' :: Range Integer
ri' = R.linearFrom 0 (- 2^127) (2^127)

ri'' :: Range Integer
ri'' = R.exponentialFrom 0 (-340282366920938463463374607431768211456) 340282366920938463463374607431768211456

rn :: Range Natural
rn = R.linear 0 (2^128)

rf :: Range Float
rf = R.exponentialFloatFrom 0 (-3.4028235e38) 3.4028235e38

rd :: Range Double
rd = R.exponentialFloatFrom 0 (-1.7976931348623157e308) 1.7976931348623157e308

ord :: Gen Ordering
ord = G.element [LT, EQ, GT]

f32 :: Gen Float
f32 = gen_flt $ G.float rf

f64 :: Gen Double
f64 = gen_flt $ G.double rd

rat :: Gen (Ratio Integer)
rat = G.frequency [(49, gen), (1, G.element [-1 :% 0, 1 :% 0, 0 :% 0])]
  where gen = G.realFrac_ (R.linearFracFrom 0 (- 2^127) (2^127))

pos :: Gen (Ratio Natural)
pos = G.frequency [(49, gen), (1, G.element [1 :% 0, 0 :% 0])]
  where gen = G.realFrac_ (R.linearFracFrom 0 0 (2^127))

gen_maybe :: Gen a -> Gen (Maybe a)
gen_maybe gen = G.frequency [(9, Just <$> gen), (1, pure Nothing)]

gen_lifted :: Gen a -> Gen (Lifted a)
gen_lifted gen = G.frequency [(9, Right <$> gen), (1, pure $ Left ())]

gen_lowered :: Gen a -> Gen (Lowered a)
gen_lowered gen = G.frequency [(9, Left <$> gen), (1, pure $ Right ())]

gen_extended :: Gen a -> Gen (Extended a)
gen_extended gen = G.frequency [(18, Extended <$> gen), (1, pure Bottom), (1, pure Top)]

gen_flt :: Floating a => Gen a -> Gen a 
gen_flt gen = G.frequency [(49, gen), (1, G.element [(-1/0), 1/0, 0/0])]

tests :: IO Bool
tests = checkParallel $$(discover)
