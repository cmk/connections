{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Order (
  -- * Constraint kinds
    Order
  , PartialOrder
  -- * Preorders
  , Preorder(..)
  , pcompareEq
  , pcompareOrd
  , pcompareRat
  -- * Re-exports
  , Ord((<=), (>=), max, min, compare)
  , Down(..)
) where

import safe Control.Applicative
import safe Data.Bool hiding (not)
import safe Data.Either
import safe Data.Functor.Apply
import safe Data.Functor.Identity
import safe Data.Int
import safe Data.List.NonEmpty
import safe Data.Maybe
import safe Data.Ord hiding ((<),(>))
import safe Data.Semigroup
import safe Data.Universe.Class (Finite(..))
import safe Data.Word
import safe GHC.Real
import safe Numeric.Natural
import safe Prelude hiding (Ord(..),Bounded)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Set as Set

type Order = Ord

type PartialOrder a = (Preorder a, Eq a)

-- | A < https://en.wikipedia.org/wiki/Preorder preorder > on /a/.
--
-- A preorder relation '<~' must satisfy the following two axioms:
--
-- \( \forall x: x \leq x \) (reflexivity)
-- 
-- \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \) (transitivity)
--
-- If additionally we have:
--
-- \( \forall a, b: (a \leq b) \Leftrightarrow \neg (b \leq a) \) (anti-symmetry)
--
-- then /a/ is a partial order and we may define an 'Eq' instance such that the following holds:
--
-- @
-- x '~~' y = x '==' y
-- x '<~' y = x '<' y '||' x '==' y
-- @
--
class Preorder a where
    {-# MINIMAL (<~) | pcompare #-} 

    infix 4 <~, >~, <, >, ?~, ~~, /~, `pcompare`, `pmax`, `pmin`

    -- | Non-strict partial order relation on /a/.
    --
    -- '<~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x <~ y = x < y || x ~~ y
    -- > x <~ y = maybe False (<~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    --
    (<~) :: a -> a -> Bool
    x <~ y = maybe False (<~ EQ) (pcompare x y)

    -- | Converse non-strict partial order relation on /a/.
    --
    -- '>~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x >~ y = x > y || x ~~ y
    -- > x >~ y = maybe False (>~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    --
    (>~) :: a -> a -> Bool
    (>~) = flip (<~)

    -- | Strict partial order relation on /a/.
    --
    -- '<' is irreflexive, asymmetric, and transitive.
    --
    -- > x < y = x <~ y && not (y <~ x)
    -- > x < y = maybe False (< EQ) (pcompare x y)
    --
    -- When '<~' is antisymmetric then /a/ is a partial 
    -- order and we have:
    -- 
    -- > x > y = x >~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    --
    (<) :: a -> a -> Bool
    x < y = x <~ y && not (y <~ x)

    -- | Converse strict partial order relation on /a/.
    --
    -- '>' is irreflexive, asymmetric, and transitive.
    --
    -- > x > y = x >~ y && not (y >~ x)
    -- > x > y = maybe False (> EQ) (pcompare x y)
    -- 
    -- When '<~' is antisymmetric then /a/ is a partial 
    -- order and we have:
    -- 
    -- > x > y = x >~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    --
    (>) :: a -> a -> Bool
    x > y = x >~ y && not (y >~ x)

    -- | Comparability relation on /a/. 
    --
    -- '?~' is reflexive, symmetric, and transitive.
    --
    -- If /a/ implements 'Ord' then we should have @x ?~ y = True@.
    --
    (?~) :: a -> a -> Bool
    x ?~ y = x <~ y || x >~ y
    
    -- | Equivalence relation on /a/.
    --
    -- '~~' is reflexive, symmetric, and transitive.
    --
    -- > x ~~ y = x <~ y && y <~ x
    -- > x ~~ y = maybe False (~~ EQ) (pcompare x y)
    --
    -- Use this as a lawful substitute for '==' when comparing
    -- floats, doubles, or rationals.
    --
    -- If /a/ implements 'Eq' then we should have @('~~') = ('==')@.
    --
    (~~) :: a -> a -> Bool
    (~~) x y = x <~ y && y <~ x

    -- | Negation of '~~'.
    --
    (/~) :: a -> a -> Bool
    x /~ y = not $ x ~~ y

    -- | A partial version of 'Data.Ord.max'. 
    --
    -- Returns the left-hand argument in the case of equality.
    --
    pmax :: a -> a -> Maybe a
    pmax x y = do
      o <- pcompare x y
      case o of
        GT -> Just x
        EQ -> Just x
        LT -> Just y

    -- | A partial version of 'Data.Ord.min'. 
    --
    -- Returns the left-hand argument in the case of equality.
    --
    pmin :: a -> a -> Maybe a
    pmin x y = do
      o <- pcompare x y
      case o of
        GT -> Just y
        EQ -> Just x
        LT -> Just x
    
    -- | Similarity relation on /a/. 
    --
    -- 'similar' is reflexive and symmetric, but not necessarily transitive.
    --
    -- Note this is only equivalent to '==' in a total (i.e. linear) order:
    --
    -- > similar (0/0 :: Float) 5 = True
    --
    -- If /a/ implements 'Ord' then we should have @('~~') = 'similar' = ('==')@.
    --
    similar :: a -> a -> Bool
    similar x y = not (x < y) && not (x > y)

    -- | A partial version of 'Data.Ord.compare'.
    --
    -- > x <  y = maybe False (<  EQ) (pcompare x y)
    -- > x >  y = maybe False (>  EQ) (pcompare x y)
    -- > x <~ y = maybe False (<~ EQ) (pcompare x y)
    -- > x >~ y = maybe False (>~ EQ) (pcompare x y)
    -- > x ~~ y = maybe False (~~ EQ) (pcompare x y)
    -- > x ?~ y = maybe False (const True) (pcompare x y)
    -- 
    -- If /a/ implements 'Ord' then we should have @'pcompare' x y = 'Just' '$' 'compare' x y@.
    --
    pcompare :: a -> a -> Maybe Ordering
    pcompare x y 
      | x <~ y    = Just $ if y <~ x then EQ else LT
      | y <~ x    = Just GT
      | otherwise = Nothing

-- | Version of 'pcompare' that uses a semiorder relation and '=='.
--
-- See <https://en.wikipedia.org/wiki/Semiorder>.
--
pcompareEq :: Eq a => (a -> a -> Bool) -> a -> a -> Maybe Ordering
pcompareEq lt x y
  | lt x y = Just LT
  | x == y = Just EQ
  | lt y x = Just GT
  | otherwise = Nothing

-- | Version of 'pcompare' that uses 'compare'.
--
pcompareOrd :: Ord a => a -> a -> Maybe Ordering
pcompareOrd x y = Just $ x `compare` y

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

newtype Total a = Total { getTotal :: a } deriving stock (Eq, Ord, Show, Functor)
  deriving Applicative via Identity

instance Ord a => Preorder (Total a) where
  x <~ y = getTotal $ liftA2 (<=) x y
  x >~ y = getTotal $ liftA2 (>=) x y
  pcompare x y = Just . getTotal $ liftA2 compare x y

deriving via (Total ()) instance Preorder ()
deriving via (Total Bool) instance Preorder Bool
deriving via (Total Ordering) instance Preorder Ordering
deriving via (Total Char) instance Preorder Char
deriving via (Total Word) instance Preorder Word
deriving via (Total Word8) instance Preorder Word8
deriving via (Total Word16) instance Preorder Word16
deriving via (Total Word32) instance Preorder Word32
deriving via (Total Word64) instance Preorder Word64
deriving via (Total Natural) instance Preorder Natural
deriving via (Total Int) instance Preorder Int
deriving via (Total Int8) instance Preorder Int8
deriving via (Total Int16) instance Preorder Int16
deriving via (Total Int32) instance Preorder Int32
deriving via (Total Int64) instance Preorder Int64
deriving via (Total Integer) instance Preorder Integer

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- N5 lattice ordering: NInf <= NaN <= PInf
n5 :: (Ord a, Fractional a) => a -> a -> Bool
n5 x y | x /= x && y /= y = True
       | x /= x = y == 1/0
       | y /= y = x == -1/0
       | otherwise = x <= y

instance Preorder Float where
  (<~) = n5

instance Preorder Double where
  (<~) = n5

-- N5 lattice comparison
{-
pinf = 1 :% 0
ninf = (-1) :% 0
anan = 0 :% 0

λ> pcompareRat anan pinf
Just LT
λ> pcompareRat pinf anan
Just GT
λ> pcompareRat anan anan
Just EQ
λ> pcompareRat anan (3 :% 5)
Nothing
-}
pcompareRat :: Ratio Integer -> Ratio Integer -> Maybe Ordering
pcompareRat (0:%0) (x:%0) = Just $ compare 0 x
pcompareRat (x:%0) (0:%0) = Just $ compare x 0
pcompareRat (x:%0) (y:%0) = Just $ compare (signum x) (signum y)
pcompareRat (0:%0) _ = Nothing
pcompareRat _ (0:%0) = Nothing
pcompareRat _ (x:%0) = Just $ compare 0 x -- guard against div-by-zero exceptions
pcompareRat (x:%0) _ = Just $ compare x 0
pcompareRat x y = Just $ compare x y

-- N5 lattice comparison
pcomparePos :: Ratio Natural -> Ratio Natural -> Maybe Ordering
pcomparePos (0:%0) (x:%0) = Just $ compare 0 x
pcomparePos (x:%0) (0:%0) = Just $ compare x 0
pcomparePos (_:%0) (_:%0) = Just EQ -- all non-nan infs are equal
pcomparePos (0:%0) (0:%_) = Just $ GT
pcomparePos (0:%_) (0:%0) = Just $ LT
pcomparePos (0:%0) _ = Nothing
pcomparePos _ (0:%0) = Nothing
pcomparePos (x:%y) (x':%y') = Just $ compare (x*y') (x'*y)

instance Preorder (Ratio Integer) where
  pcompare = pcompareRat

instance Preorder (Ratio Natural) where
  pcompare = pcomparePos

instance Preorder a => Preorder (Down a) where
  (Down x) <~ (Down y) = y <~ x
  pcompare (Down x) (Down y) = pcompare y x

instance Preorder a => Preorder (Dual a) where
  (Dual x) <~ (Dual y) = y <~ x
  pcompare (Dual x) (Dual y) = pcompare y x

instance Preorder a => Preorder (Max a) where
  Max a <~ Max b = a <~ b

instance Preorder a => Preorder (Min a) where
  Min a <~ Min b = a <~ b

instance Preorder Any where
  Any x <~ Any y = x <~ y

instance Preorder All where
  All x <~ All y = y <~ x

-- Canonical semigroup ordering
instance Preorder a => Preorder (Maybe a) where
  Nothing <~ _ = True
  Just{} <~ Nothing = False
  Just a <~ Just b = a <~ b

instance Preorder a => Preorder [a] where
  {-# SPECIALISE instance Preorder [Char] #-}
  [] <~ _     = True
  (_:_) <~ [] = False
  (x:xs) <~ (y:ys) = x <~ y && xs <~ ys

{-
  pcompare []     []     = Just EQ
  pcompare []     (_:_)  = Just LT
  pcompare (_:_)  []     = Just GT
  pcompare (x:xs) (y:ys) = case pcompare x y of
                              Just EQ -> pcompare xs ys
                              other   -> other
-}

instance Preorder a => Preorder (NonEmpty a) where
  (x :| xs) <~ (y :| ys) = x <~ y && xs <~ ys

-- Canonical semigroup ordering
instance (Preorder a, Preorder b) => Preorder (Either a b) where
  Right a <~ Right b  = a <~ b
  Right _ <~ _        = False

  Left a <~ Left b   = a <~ b
  Left _ <~ _        = True
 
-- Canonical semigroup ordering
instance (Preorder a, Preorder b) => Preorder (a, b) where 
  (a,b) <~ (i,j) = a <~ i && b <~ j

instance (Preorder a, Preorder b, Preorder c) => Preorder (a, b, c) where 
  (a,b,c) <~ (i,j,k) = a <~ i && b <~ j && c <~ k

instance (Preorder a, Preorder b, Preorder c, Preorder d) => Preorder (a, b, c, d) where 
  (a,b,c,d) <~ (i,j,k,l) = a <~ i && b <~ j && c <~ k && d <~ l

instance (Preorder a, Preorder b, Preorder c, Preorder d, Preorder e) => Preorder (a, b, c, d, e) where 
  (a,b,c,d,e) <~ (i,j,k,l,m) = a <~ i && b <~ j && c <~ k && d <~ l && e <~ m

instance Ord a => Preorder (Set.Set a) where
    (<~) = Set.isSubsetOf

instance (Ord k, Preorder a) => Preorder (Map.Map k a) where
    (<~) = Map.isSubmapOfBy (<~)

instance Preorder a => Preorder (IntMap.IntMap a) where
    (<~) = IntMap.isSubmapOfBy (<~)

instance Preorder IntSet.IntSet where
    (<~) = IntSet.isSubsetOf

-- check semimodules paper
instance (Finite a, Preorder b) => Preorder (a -> b) where
  pcompare f g = mconcat [f x `pcompare` g x | x <- universeF]

instance (Finite a, Preorder a) => Preorder (Endo a) where
  pcompare (Endo f) (Endo g) = pcompare f g

