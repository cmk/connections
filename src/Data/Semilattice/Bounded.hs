{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Semilattice.Bounded where

import Control.Applicative
import Data.Data (Data, Typeable)
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import Data.Semilattice
import Data.Semifield
import GHC.Generics (Generic, Generic1)
import Data.Float

import Prelude hiding (Bounded)

type IEEE a = Nan (Bounded a)

data Bounded a = Bot | Fin a | Top
  deriving (Show, Generic, Generic1, Functor, Foldable, Traversable)

instance Prd a => Prd (Bounded a) where
    Bot <~ _ = True
    _ <~ Bot = False
    _ <~ Top = True
    Top <~ _ = False
    Fin a <~ Fin b = a <~ b

instance Prd a => Minimal (Bounded a) where
    minimal = Bot

instance Prd a => Maximal (Bounded a) where
    maximal = Top

{-
instance Covered (Bounded Float) where
  Bounded x <. Bounded y = shiftf 1 x == y

instance Graded (Bounded Float) where
  rank (Bounded x) | indeterminate x = 0
                   | otherwise = r where
    x' = floatInt32 x
    y' = floatInt32 ninf
    r = fromIntegral . abs $ x' - y'
-}

bounded :: b -> (a -> b) -> b -> Bounded a -> b
bounded b _ _ Bot = b
bounded _ f _ (Fin a) = f a
bounded _ _ b Top = b

-- | Interpret @'Bounded' a@ using the 'BoundedLattice' of @a@.
--
-- This map is monotone when /f/ is.
--
bounded' :: BoundedLattice b => (a -> b) -> Bounded a -> b
bounded' f = bounded bottom f top

upperBounded :: UpperBoundedLattice b => (a -> b) -> Bounded a -> Maybe b
upperBounded f = bounded Nothing (Just . f) (Just top)

isBot :: Bounded a -> Bool
isBot = bounded True (const False) False

isTop :: Bounded a -> Bool
isTop = bounded False (const False) True

isFin :: Bounded a -> Bool
isFin = bounded False (const True) False

-- Lift all exceptional values
liftField :: Bound a => Field a => (a -> b) -> a -> IEEE b
liftField f = liftNan $ liftBounded f 

-- This map is a lattice morphism when /f/ is.
liftBot :: Minimal a => (a -> b) -> a -> Bounded b
liftBot f = g where
  g i | i =~ minimal = Bot
      | otherwise = Fin $ f i

liftTop :: Maximal a => (a -> b) -> a -> Bounded b
liftTop f = g where
  g i | i =~ maximal = Top
      | otherwise = Fin $ f i

liftBounded :: Bound a => (a -> b) -> a -> Bounded b
liftBounded f = g where
  g x | x =~ maximal = Top
      | x =~ minimal = Bot
      | otherwise = Fin (f x)



{-

instance Applicative Nan where
    pure = Def
    Nan <*> _ = Nan
    Def f <*> x = f <$> x

instance Num a => Num (Nan a) where
    negate      = fmap negate
    (+)         = liftA2 (+)
    (*)         = liftA2 (*)
    fromInteger = pure . fromInteger
    abs         = fmap abs
    signum      = fmap signum





defnan :: Prd a => Prd b => Conn a b -> Conn (Nan a) (Nan b)
defnan conn = Conn f g where 
  Conn f' g' = right conn
  f = eitherNan . f' . nanEither ()
  g = eitherNan . g' . nanEither ()

defnan' :: Prd a => Prd b => Trip a b -> Trip (Nan a) (Nan b)
defnan' trip = Trip f g h where 
  Trip f' g' h' = right' trip
  f = eitherNan . f' . nanEither ()
  g = eitherNan . g' . nanEither () 
  h = eitherNan . h' . nanEither () 

--nanfld :: Prd a => Field a => Trip (Nan a) a
-- Field a => Field (Nan a)
-- /Caution/ this is only legal if (Nan a) has no nans.
fldnan :: Prd a => Fractional a => Trip a (Nan a)
fldnan = Trip f g f where
  f a = if a =~ (0/0) then Nan else Def a 
  g = nan (0/0) id


instance Semigroup a => Semigroup (Nan a) where
instance Semiring a => Semiring (Nan a) where
instance Semifield a => Semifield (Nan a) where

instance Group a => Group (Nan a) where
instance Ring a => Ring (Nan a) where

instance Field a => Field (Nan a) where

u + Nan = Nan + u = Nan − Nan = Nan
u · Nan = Nan · u = Nan Nan−1 = Nan
Nan  u ⇔ u = Nan u  Nan ⇔ u = Nan
-}

