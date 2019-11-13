{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Safe                #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types       #-}

module Data.Prd.Nan where

import Control.Applicative
import Data.Data (Data, Typeable)
import Data.Prd
import Data.Connection
import GHC.Generics (Generic, Generic1)

-- A type with an additional element allowing for the possibility of undefined values.
-- Isomorphic to /Maybe a/ but with a different 'Prd' instance.
data Nan a = Nan | Def a
  deriving ( Eq, Ord, Show, Data, Typeable, Generic, Generic1, Functor, Foldable, Traversable)

nan :: b -> (a -> b) -> Nan a -> b
nan _ f (Def y) = f y
nan x _  Nan    = x 

defined :: Nan a -> Bool
defined Nan = False
defined _   = True

mapNan :: (a -> b) -> Nan a -> Nan b
mapNan f = nan Nan $ Def . f

maybeNan :: (forall a. a -> a) -> Maybe a -> Nan a
maybeNan _ Nothing = Nan
maybeNan f (Just x) = Def $ f x

nanMaybe :: (forall a. a -> a) -> Nan a -> Maybe a
nanMaybe _ Nan = Nothing
nanMaybe f (Def x) = Just $ f x

eitherNan :: Either a b -> Nan b
eitherNan = either (const Nan) Def

nanEither :: a -> Nan b -> Either a b
nanEither x = nan (Left x) Right

liftNan :: (Prd a, Fractional a) => (a -> b) -> a -> Nan b
liftNan f x | x =~ (0/0) = Nan
            | otherwise = Def (f x)

liftNan' :: RealFloat a => (a -> b) -> a -> Nan b
liftNan' f x | isNaN x = Nan
             | otherwise = Def (f x)

-- Lift all exceptional values
liftAll :: (RealFloat a, Prd a, Bound b) => (a -> b) -> a -> Nan b
liftAll f x | isNaN x = Nan
            | isInf x = Def maximal
            | isInf (-x) = Def minimal
            | otherwise = Def (f x)

isInf :: (RealFloat a, Prd a) => a -> Bool
isInf x = isInfinite x && gt x 0

floatOrdering :: (RealFloat a, Prd a) => Trip a (Nan Ordering)
floatOrdering = Trip f g h where

  g (Def GT) = 1/0
  g (Def LT) = - 1/0
  g (Def EQ) = 0
  g Nan = 0/0
  
  f x | isNaN x    = Nan
  f x | isInf (-x) = Def LT
  f x | x <~ 0     = Def EQ
  f x | otherwise  = Def GT

  h x | isNaN x    = Nan
  h x | isInf x    = Def GT
  h x | x >~ 0     = Def EQ
  h x | otherwise  = Def LT

instance Prd a => Prd (Nan a) where
    Nan <~ Nan = True
    _   <~ Nan = False
    Nan <~ _   = False
    Def a <~ Def b = a <~ b

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

nanflt :: Prd a => Fractional a => Conn (Nan a) a
nanflt = Conn (nan (0/0) id) $ \y -> if y =~ (0/0) then Nan else Def y 

def :: Prd a => Prd b => Conn a b -> Conn (Nan a) (Nan b)
def conn = Conn f g where 
  Conn f' g' = right conn
  f = eitherNan . f' . nanEither ()
  g = eitherNan . g' . nanEither ()

{-
floatOrdering :: Trip Float (Nan Ordering)
floatOrdering = Trip f g h where
  h x | isNaN x = Nan
  h x | posinf x = Def GT
  h x | finite x && x >~ 0 = Def EQ
  h x | otherwise = Def LT

  g (Def GT) = maxBound
  g (Def LT) = minBound
  g (Def EQ) = 0
  g Nan = aNan
  
  f x | isNaN x = Nan
  f x | neginf x = Def LT
  f x | finite x && x <~ 0 = Def EQ
  f x | otherwise = Def GT


_Def' :: Prd a => Prd b => Trip a b -> Trip (Nan a) (Nan b)
_Def' trip = Trip f g h where 
  Trip f' g' h' = _R' trip
  f = eitherNan . f' . nanEither ()
  g = eitherNan . g' . nanEither () 
  h = eitherNan . h' . nanEither () 


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

