{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Prd.Inf where

import Control.Applicative
import Data.Data (Data, Typeable)
import Data.Prd
import Data.Prd.Nan
import Data.Connection
import GHC.Generics (Generic, Generic1)

data Inf a = Nnf | Fin a | Pnf
  deriving ( Eq, Ord, Show, Generic, Generic1, Functor, Foldable, Traversable)

instance Prd a => Prd (Inf a) where
    Nnf <~ _ = True
    _ <~ Nnf = False
    _ <~ Pnf = True
    Pnf <~ _ = False
    Fin a <~ Fin b = a <~ b

instance Prd a => Minimal (Inf a) where
    minimal = Nnf

instance Prd a => Maximal (Inf a) where
    maximal = Pnf

instance Bounded (Inf a) where
    minBound = Nnf
    maxBound = Pnf

inf :: b -> (a -> b) -> b -> Inf a -> b
inf b _ _ Nnf = b
inf _ f _ (Fin a) = f a
inf _ _ b Pnf = b

isNnf :: Inf a -> Bool
isNnf = inf True (const False) False

isPnf :: Inf a -> Bool
isPnf = inf False (const False) True

isFin :: Inf a -> Bool
isFin = inf False (const True) False

-- Lift all exceptional values
liftInf :: (RealFloat a, Prd a, Bound b) => (a -> b) -> a -> Inf b
liftInf f x | isInf x = Pnf
            | isInf (-x) = Nnf
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

