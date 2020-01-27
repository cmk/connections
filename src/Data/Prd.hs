-- {-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE CPP       #-}
module Data.Prd (
    module Data.Prd
  , Down(..)
) where

import Control.Applicative
import Control.Monad
import Data.Data (Data, Typeable)
import Data.Function
import Data.Int as Int (Int, Int8, Int16, Int32, Int64)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (First, Last)
import Data.Ord (Down(..))
import Data.Ratio
import Data.Word (Word, Word8, Word16, Word32, Word64)
import GHC.Generics (Generic, Generic1)
import GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import Numeric.Natural
import Data.Semigroup (Min(..), Max(..))
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import Data.Semiring
import Data.Semifield (Field, Semifield, anan, pinf, ninf)
import Data.Fixed
import qualified Data.Semigroup as S
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Sequence as Seq

import Prelude hiding (Fractional(..),Num(..))

infix 4 <~, >~, /~, ~~, =~, ?~, `pgt`, `pge`, `peq`, `pne`, `ple`, `plt`

infix 4 `lt`, `gt`, `le`, `ge`, `eq`, `ne`, `pmax`, `pmin`


-- | A partial order on the set /a/.
--
-- A poset relation '<~' must satisfy the following three partial order axioms:
--
-- \( \forall x: x \leq x \) (reflexivity)
-- 
-- \( \forall a, b: (a \leq b) \Leftrightarrow \neg (b \leq a) \) (anti-symmetry)
--
-- \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \) (transitivity)
--
-- If a prior equality relation is available, then a valid @Prd a@ instance may be derived from a semiorder relation 'lt' as:
--
-- @
-- x '<~' y = 'lt' x y '||' x '==' y
-- @
--
-- If /a/ is derived from a semiorder then the definition of 'lt' must satisfy 
-- the three semiorder axioms:
--
-- \( \forall x, y: x \lt y \Rightarrow \neg y \lt x \) (asymmetry)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \sim z \wedge z \lt w \Rightarrow x \lt w \) (2-2 chain)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \lt z \wedge y \sim w \Rightarrow \neg (x \sim w \wedge z \sim w) \) (3-1 chain)
--
-- The poset axioms on '<~' then follow from the first & second axioms on 'lt',
-- however the converse is not true. While the first semiorder axiom on 'lt' follows, the second 
-- and third semiorder axioms forbid partial orders of four items forming two disjoint chains: 
--
-- * the second axiom forbids two chains of two items each (the (2+2) free poset)
-- * the third axiom forbids a three-item chain with one unrelated item
--
-- See also the wikipedia definitions of <https://en.wikipedia.org/wiki/Partially_ordered_set partially ordered set>
-- and <https://en.wikipedia.org/wiki/Semiorder semiorder>.
--
class Prd a where
  {-# MINIMAL (<~) | (>~) #-} 

  -- | Non-strict partial order relation on /a/.
  --
  -- '<~' is reflexive, anti-symmetric, and transitive.
  --
  (<~) :: a -> a -> Bool
  (<~) = flip (>~)

  -- | Converse non-strict partial order relation on /a/.
  --
  -- '>~' is reflexive, anti-symmetric, and transitive.
  --
  (>~) :: a -> a -> Bool
  (>~) = flip (<~)

  -- | Equivalence relation on /a/.
  --
  -- '=~' is reflexive, symmetric, and transitive.
  --
  -- @ x =~ y = maybe False (== EQ) (pcomparePrd x y)
  --
  -- If /a/ implements 'Eq' then (ideally) @x =~ y = x == y@.
  --
  (=~) :: a -> a -> Bool
  x =~ y = x <~ y && x >~ y

  -- | Comparability relation on /a/. 
  --
  -- '?~' is reflexive, symmetric, and transitive.
  --
  -- @ x ?~ y = maybe False (const True) (pcomparePrd x y) @
  --
  -- If /a/ implements 'Ord' then (ideally) @x ?~ y = True@.
  --
  (?~) :: a -> a -> Bool
  x ?~ y = x <~ y || x >~ y

  pcompare :: a -> a -> Maybe Ordering
  pcompare x y 
    | x <~ y = Just $ if y <~ x then EQ else LT
    | y <~ x = Just GT
    | otherwise = Nothing


type Bound a = (Minimal a, Maximal a) 

-- | A minimal element of a partially ordered set.
-- 
-- @ 'minimal' '?~' a ==> 'minimal' '<~' a @
--
-- Note that 'minimal' needn't be comparable to all values in /a/.
--
-- When /a/ is a 'Field' @ 'minimal' = 'ninf' @
--
-- See < https://en.wikipedia.org/wiki/Maximal_and_minimal_elements >.
--
class Prd a => Minimal a where
    minimal :: a

-- | A maximal element of a partially ordered set.
-- 
-- @ 'maximal' '?~' a ==> 'maximal' '>~' a @
--
-- Note that 'maximal' needn't be comparable to all values in /a/.
--
-- When /a/ is a 'Semifield' @ 'maximal' = 'pinf' @
--
-- See < https://en.wikipedia.org/wiki/Maximal_and_minimal_elements >.
--
class Prd a => Maximal a where
    maximal :: a


-- | Similarity relation on /a/. 
--
-- '~~' is reflexive and symmetric, but not necessarily transitive.
--
-- Note this is only equivalent to '==' in a total (i.e. linear) order.
--
(~~) :: Prd a => a -> a -> Bool
x ~~ y = not (x `lt` y) && not (x `gt` y)

-- | Negation of '~~'.
--
(/~) :: Prd a => a -> a -> Bool
x /~ y = not $ x ~~ y

-- | Version of 'pcompare' that uses '=='.
--
pcompareEq :: Eq a => Prd a => a -> a -> Maybe Ordering
pcompareEq x y
  | x `lt` y  = Just LT
  | x  ==  y  = Just EQ
  | x `gt` y  = Just GT
  | otherwise = Nothing

-- | Version of 'pcompare' that uses 'compare'.
--
pcompareOrd :: Ord a => a -> a -> Maybe Ordering
pcompareOrd x y = Just $ x `compare` y

-- | Strict partial order relation on /a/.
--
-- 'lt' is irreflexive, asymmetric, and transitive.
--
-- @ lt x y = maybe False (< EQ) (pcompare x y) @
--
-- If /a/ implements 'Ord' then (ideally) @x `lt` y = x < y@.
--
lt :: Prd a => a -> a -> Bool
x `lt` y | x ?~ y = x <~ y && x `ne` y
         | otherwise = False

-- | Prefix version of '<~'.
--
-- @ le x y = maybe False (<= EQ) (pcomparePrd x y)
--
le :: Prd a => a -> a -> Bool
x `le` y = x <~ y

-- | Prefix version of '=~'.
--
-- @ eq x y = maybe False (== EQ) (pcomparePrd x y)
--
eq :: Prd a => a -> a -> Bool
x `eq` y = x <~ y && x >~ y

-- | Negation of 'eq'.
--
-- @ ne x y = maybe False (/= EQ) (pcomparePrd x y)
--
ne :: Prd a => a -> a -> Bool
x `ne` y = not $ x `eq` y

-- | Prefix version of '>~'.
--
-- @ ge x y = maybe False (>= EQ) (pcomparePrd x y)
--
ge :: Prd a => a -> a -> Bool
x `ge` y = x >~ y

-- | Converse strict partial order relation on /a/.
--
-- 'gt' is irreflexive, asymmetric, and transitive.
--
-- @ gt x y = maybe False (> EQ) (pcompare x y) @
--
-- If /a/ implements 'Ord' then (ideally) @x `gt` y = x > y@.
--
gt :: Prd a => a -> a -> Bool
x `gt` y | x ?~ y = x >~ y && x `ne` y
         | otherwise = False

-- | A partial version of ('=~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
peq  :: Prd a => a -> a -> Maybe Bool
peq x y = case x `pcompare` y of
     Just EQ -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of ('/~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pne :: Prd a => a -> a -> Maybe Bool
pne x y = case x `pcompare` y of
     Just EQ -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('<~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
ple :: Prd a => a -> a -> Maybe Bool
ple x y = case x `pcompare` y of
     Just GT -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('>~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pge :: Prd a => a -> a -> Maybe Bool
pge x y = case x `pcompare` y of
     Just LT -> Just False
     Just _  -> Just True
     Nothing -> Nothing

-- | A partial version of ('<')  
-- 
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @lt x y == maybe False id $ plt x y@
--
plt :: Prd a => a -> a -> Maybe Bool
plt x y = case x `pcompare` y of
     Just LT -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of ('>')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @gt x y == maybe False id $ pgt x y@
--
pgt :: Prd a => a -> a -> Maybe Bool
pgt x y = case x `pcompare` y of
     Just GT -> Just True
     Just _  -> Just False
     Nothing -> Nothing

-- | A partial version of 'Data.Ord.max'. 
--
-- Returns the right argument in the case of equality.
--
pmax :: Prd a => a -> a -> Maybe a
pmax x y = do
  o <- pcompare x y
  case o of
    GT -> Just x
    EQ -> Just y
    LT -> Just y

pjoin :: Minimal a => Foldable f => f a -> Maybe a
pjoin = foldM pmax minimal

-- | A partial version of 'Data.Ord.min'. 
--
-- Returns the right argument in the case of equality.
--
pmin :: Prd a => a -> a -> Maybe a
pmin x y = do
  o <- pcompare x y
  case o of
    GT -> Just y
    EQ -> Just x
    LT -> Just x

pmeet :: Maximal a => Foldable f => f a -> Maybe a
pmeet = foldM pmin maximal


--TODO remove Eq reqs
sign :: (Additive-Monoid) a => Prd a => a -> Maybe Ordering
sign x = pcompare x zero

positive :: (Additive-Monoid) a => Prd a => a -> Bool
positive x = sign x == Just GT

negative :: (Additive-Monoid) a => Prd a => a -> Bool
negative x = sign x == Just LT

indeterminate :: (Additive-Monoid) a => Prd a => a -> Bool
indeterminate x = sign x == Nothing


isAnan :: Prd a => Semifield a => a -> Bool
isAnan a = a =~ anan

-- /Caution/ 'Eq' instance for some 'Semifield' types is either 
-- unlawful (e.g. 'Float), or exceptional (e.g. 'Rational').
isPinf :: Prd a => Semifield a => a -> Bool
isPinf a = a =~ pinf

isNinf :: Prd a => Field a => a -> Bool
isNinf a = a =~ ninf

finite' :: Prd a => Field a => a -> Bool
finite' = finite * not . isNinf

finite :: Prd a => Semifield a => a -> Bool
finite = not . isAnan * not . isPinf


---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

instance Prd a => Prd [a] where
    {-# SPECIALISE instance Prd [Char] #-}
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

instance Prd a => Prd (NonEmpty a) where
    (x :| xs) <~ (y :| ys) = x <~ y && xs <~ ys

instance Prd a => Prd (Down a) where
    (Down x) <~ (Down y) = y <~ x
    pcompare (Down x) (Down y) = pcompare y x

-- Canonically ordered.
instance Prd a => Prd (Dual a) where
    (Dual x) <~ (Dual y) = y <~ x
    pcompare (Dual x) (Dual y) = pcompare y x

instance Prd a => Prd (S.Max a) where S.Max a <~ S.Max b = a <~ b --TODO push upstream
instance Prd a => Prd (S.Min a) where S.Min a <~ S.Min b = a <~ b --TODO push upstream

instance Prd Any where
    Any x <~ Any y = x <~ y

instance Prd All where
    All x <~ All y = y <~ x

{-

-- | 'First a' forms a pre-dioid for any semigroup @a@.
instance (Eq a, Semigroup a) => Prd (S.First a) where 
    (<~) = (==)

instance Ord a => Prd (S.Maximal a) where 
    pcompare (S.Maximal x) (S.Maximal y) = Just $ compare x y

instance Ord a => Prd (S.Minimal a) where 
    pcompare (S.Minimal x) (S.Minimal y) = Just $ compare y x

-}

instance Prd Float where
    x <~ y | x /= x && y /= y = True 
           | x /= x || y /= y = False
           | otherwise        = x <= y
{-
    pcompare x y | x /= x && y /= y = Just EQ 
                 | x /= x || y /= y = Nothing
                 | otherwise        = pcompareOrd x y

    x `eq` y | x /= x && y /= y = True
             | x /= x || y /= y = False
             | otherwise = x == y

    x `lt` y | x /= x || y /= y = False
             | otherwise = shift 2 x P.< y
-}



instance Prd Double where
    x <~ y | x /= x && y /= y = True 
           | x /= x || y /= y = False
           | otherwise        = x <= y

instance Prd (Ratio Integer)  where
{-
    (x:%y) <~ (x':%y') | (x `eq` 0 && y `eq` 0) && (x' `eq` 0 && y' `eq` 0) = True
                       | (x `eq` 0 && y `eq` 0) || (x' `eq` 0 && y' `eq` 0) = False
                       | y `eq` 0 = if x > 0 then False else True
                       | y' `eq` 0 = if x' > 0 then True else False
                       | otherwise = x * signum y * y' >~ x' * signum y' * y
-}
-- | isNan r && isNan r'
    r@(x:%y) <~ r'@(x':%y') | (x `eq` 0 && y `eq` 0) && (x' `eq` 0 && y' `eq` 0) = True
                            | (x `eq` 0 && y `eq` 0) || (x' `eq` 0 && y' `eq` 0) = False
                            | (x `eq` x' && y `eq` y') || (x * y' `eq` y * x') = True
                            | y `eq` 0 = if x > 0 then False else True
                            | y' `eq` 0 = if x' > 0 then True else False
                            | x `eq` 0 || x' `eq` 0 = x <= x'
                            | otherwise = r <= r' --x * signum y * y' >~ x' * signum y' * y

instance Prd (Ratio Natural)  where
    (x:%y) <~ (x':%y') | (x `eq` 0 && y `eq` 0) && (x' `eq` 0 && y' `eq` 0) = True
                       | (x `eq` x' && y `eq` y') || x * y' `eq` y * x' = True
                       | (x `eq` 0 && y `eq` 0) || (x' `eq` 0 && y' `eq` 0) = False
                       | y `eq` 0 = False
                       | y' `eq` 0 = True
                       | otherwise = x * y' >~ x' * y

-- Canonical semigroup ordering
instance Prd a => Prd (Maybe a) where
    Just a <~ Just b = a <~ b
    x@Just{} <~ Nothing = False
    Nothing <~ _ = True

-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (Either a b) where
    Right a <~ Right b  = a <~ b
    Right _ <~ _        = False
    
    Left e <~ Left f   = e <~ f
    Left _ <~ _        = True
 
-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (a, b) where 
  (a,b) <~ (i,j) = a <~ i && b <~ j

instance (Prd a, Prd b, Prd c) => Prd (a, b, c) where 
  (a,b,c) <~ (i,j,k) = a <~ i && b <~ j && c <~ k

instance (Prd a, Prd b, Prd c, Prd d) => Prd (a, b, c, d) where 
  (a,b,c,d) <~ (i,j,k,l) = a <~ i && b <~ j && c <~ k && d <~ l

instance (Prd a, Prd b, Prd c, Prd d, Prd e) => Prd (a, b, c, d, e) where 
  (a,b,c,d,e) <~ (i,j,k,l,m) = a <~ i && b <~ j && c <~ k && d <~ l && e <~ m

instance Ord a => Prd (Set.Set a) where
    (<~) = Set.isSubsetOf

instance (Ord k, Prd a) => Prd (Map.Map k a) where
    (<~) = Map.isSubmapOfBy (<~)

instance Prd a => Prd (IntMap.IntMap a) where
    (<~) = IntMap.isSubmapOfBy (<~)

instance Prd IntSet.IntSet where
    (<~) = IntSet.isSubsetOf


#define derivePrd(ty)         \
instance Prd ty where {       \
   (<~) = (<=)                \
;  {-# INLINE (<~) #-}        \
;  pcompare = pcompareOrd     \
;  {-# INLINE pcompare #-}    \
}





{-
instance Prd Bool where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Char where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Integer where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int where 
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int8 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int16 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int32 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Int64 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Natural where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word8 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word16 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word32 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Word64 where
    (<~) = (<=)
    pcompare = pcompareOrd

instance Prd Ordering where
    (<~) = (<=)
    pcompare = pcompareOrd
-}



derivePrd(())
derivePrd(Bool)
derivePrd(Char)
derivePrd(Ordering)

derivePrd(Int)
derivePrd(Int8)
derivePrd(Int16)
derivePrd(Int32)
derivePrd(Int64)
derivePrd(Integer)

derivePrd(Word)
derivePrd(Word8)
derivePrd(Word16)
derivePrd(Word32)
derivePrd(Word64)
derivePrd(Natural)

derivePrd(Uni)
derivePrd(Deci)
derivePrd(Centi)
derivePrd(Milli)
derivePrd(Micro)
derivePrd(Nano)
derivePrd(Pico)

-------------------------------------------------------------------------------
-- Minimal
-------------------------------------------------------------------------------

instance Minimal Float where minimal = ninf

instance Minimal Double where minimal = ninf

instance Minimal Natural where minimal = 0

instance Minimal (Ratio Natural) where minimal = 0

instance Minimal IntSet.IntSet where
    minimal = IntSet.empty

instance Prd a => Minimal (IntMap.IntMap a) where
    minimal = IntMap.empty

instance Ord a => Minimal (Set.Set a) where
    minimal = Set.empty

instance (Ord k, Prd a) => Minimal (Map.Map k a) where
    minimal = Map.empty

instance (Minimal a, Minimal b) => Minimal (a, b) where
    minimal = (minimal, minimal)

instance (Minimal a, Prd b) => Minimal (Either a b) where
    minimal = Left minimal

instance Prd a => Minimal (Maybe a) where
    minimal = Nothing 

instance Maximal a => Minimal (Down a) where
    minimal = Down maximal

instance Maximal a => Minimal (Dual a) where
    minimal = Dual maximal

#define deriveMinimal(ty)            \
instance Minimal ty where {          \
    minimal = minBound               \
;   {-# INLINE minimal #-}           \
}


deriveMinimal(())
deriveMinimal(Bool)
deriveMinimal(Ordering)

deriveMinimal(Int)
deriveMinimal(Int8)
deriveMinimal(Int16)
deriveMinimal(Int32)
deriveMinimal(Int64)

deriveMinimal(Word)
deriveMinimal(Word8)
deriveMinimal(Word16)
deriveMinimal(Word32)
deriveMinimal(Word64)

-------------------------------------------------------------------------------
-- Maximal
-------------------------------------------------------------------------------

#define deriveMaximal(ty)            \
instance Maximal ty where {           \
   maximal = maxBound                \
;  {-# INLINE maximal #-}            \
}


deriveMaximal(())
deriveMaximal(Bool)
deriveMaximal(Ordering)

deriveMaximal(Int)
deriveMaximal(Int8)
deriveMaximal(Int16)
deriveMaximal(Int32)
deriveMaximal(Int64)

deriveMaximal(Word)
deriveMaximal(Word8)
deriveMaximal(Word16)
deriveMaximal(Word32)
deriveMaximal(Word64)

--instance (Prd a, Semifield a) => Maximal a where maximal = pinf

instance Maximal Float where maximal = pinf

instance Maximal Double where maximal = pinf

instance (Maximal a, Maximal b) => Maximal (a, b) where
    maximal = (maximal, maximal)

instance (Prd a, Maximal b) => Maximal (Either a b) where
    maximal = Right maximal

instance Maximal a => Maximal (Maybe a) where
    maximal = Just maximal

instance Minimal a => Maximal (Dual a) where
    maximal = Dual minimal

instance Minimal a => Maximal (Down a) where
    maximal = Down minimal





{-
instance Maximal () where maximal = ()

instance Maximal Bool where maximal = maxBound

instance Maximal Ordering where maximal = maxBound

instance Maximal Int where maximal = maxBound

instance Maximal Int8 where maximal = maxBound

instance Maximal Int16 where maximal = maxBound

instance Maximal Int32 where maximal = maxBound

instance Maximal Int64 where maximal = maxBound

instance Maximal Word where maximal = maxBound

instance Maximal Word8 where maximal = maxBound

instance Maximal Word16 where maximal = maxBound

instance Maximal Word32 where maximal = maxBound

instance Maximal Word64 where maximal = maxBound

-- works but probably want more explicit instances
instance (Prd a, (Additive-Semigroup) a) => Semigroup (Ordered a) where
  (<>) = liftA2 add

instance (Prd a, (Additive-Monoid) a) => Monoid (Ordered a) where
  mempty = pure zero
-}

{-
instance Semigroup (Max a) => Semigroup (Additive (Max a)) where
  (<>) = liftA2 (<>)

instance Monoid (Max a) => Monoid (Additive (Max a)) where
  mempty = pure mempty

instance (Ord a, Prd a, Minimal a) => Monoid (Additive (Max a)) where
  mempty = pure . pure $ minimal


instance (Additive-Semigroup) a => Semigroup (Multiplicative (Min a)) where
  Multiplicative a <> Multiplicative b = Multiplicative $ liftA2 add a b

instance (Additive-Monoid) a => Monoid (Multiplicative (Min a)) where
  mempty = pure . pure $ zero
-}

{-
-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Min a)
-- >>> zero :: Min Natural
-- Min {getMin = 0}
instance (Maximal a, Semigroup (Min a)) => Monoid (Additive (Min a)) where
  mempty = pure $ Min maximal

-- workaround for poorly specified entailment: instance (Ord a, Bounded a) => Monoid (Max a)
instance (Minimal a, Semigroup (Max a)) => Monoid (Additive (Max a)) where
  mempty = pure $ Max minimal
-}
{-
--TODO push upstream
instance Bounded a => Bounded (Down a) where
  maxBound = minBound
  minBound = maxBound
-}
-------------------------------------------------------------------------------
-- Iterators
-------------------------------------------------------------------------------

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pred rel f seed = go seed
  where go x | x' `rel` x = x
             | pred x = x
             | otherwise = go x'
          where x' = f x

{-# INLINE while #-}
while :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while pred rel f seed = go seed
  where go x | x' `rel` x = x
             | not (pred x') = x
             | otherwise = go x'
          where x' = f x

{-
while' :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while' pred rel f seed = go seed f
  where go x | x' `rel` x = id
             | not (pred x') = id
             | otherwise = go x' . f
          where x' = f x
-}

-- | Greatest (resp. least) fixed point of a monitone (resp. antitone) function. 
--
-- Does not check that the function is monitone (resp. antitone).
--
-- See also < http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem >.
--
{-# INLINE fixed #-}
fixed :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixed = while (\_ -> True)

