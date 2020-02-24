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
    Down(..)
  , Ord(min, max, compare)
  , module Data.Prd
) where

import Data.Function
import Data.Int as Int (Int, Int8, Int16, Int32, Int64)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (First, Last)
import Data.Ord (Ord, Down(..), compare, min, max)
import Data.Ratio
import Data.Word (Word, Word8, Word16, Word32, Word64)
import GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import Numeric.Natural
--import Data.Semigroup
import Data.Semiring
import Data.Semifield (Field, Semifield, anan, pinf, ninf)
import Data.Fixed
import qualified Data.Semigroup as S
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Prelude as P


import Prelude hiding (Ord(..), Fractional(..),Num(..))

infix 4 <=, >=, <, >, =~, ~~, !~, /~, ?~, `pgt`, `pge`, `peq`, `pne`, `ple`, `plt`

-- | A <https://en.wikipedia.org/wiki/Reflexive_relation reflexive> partial order on /a/.
--
-- A poset relation '<=' must satisfy the following three partial order axioms:
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
-- x '<=' y '==' 'lt' x y '||' x '==' y
-- @
--
-- If /a/ is derived from a semiorder then the definition of 'lt' must satisfy the three semiorder axioms:
--
-- \( \forall x, y: x \lt y \Rightarrow \neg y \lt x \) (asymmetry)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \sim z \wedge z \lt w \Rightarrow x \lt w \) (2-2 chain)
--
-- \( \forall x, y, z, w: x \lt y \wedge y \lt z \wedge y \sim w \Rightarrow \neg (x \sim w \wedge z \sim w) \) (3-1 chain)
--
-- The poset axioms on '<=' then follow from the first & second axioms on 'lt',
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
  {-# MINIMAL (<=) | pcompare #-} 

  -- | Non-strict partial order relation on /a/.
  --
  -- '<=' is reflexive, anti-symmetric, and transitive.
  --
  -- Furthermore we have:
  --
  -- @
  -- x '<=' y ≡ 'maybe' 'False' ('<=' 'EQ') ('pcompare' x y)
  -- x '<=' y ≡ x '<' y '||' x '=~' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  (<=) :: a -> a -> Bool
  x <= y = maybe False (P.<= EQ) $ pcompare x y

  -- | Converse non-strict partial order relation on /a/.
  --
  -- '>=' is reflexive, anti-symmetric, and transitive.
  --
  -- Furthermore we have:
  --
  -- @
  -- x '>=' y ≡ 'maybe' 'False' ('>=' 'EQ') ('pcompare' x y)
  -- x '>=' y ≡ x '>' y '||' x '=~' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  (>=) :: a -> a -> Bool
  (>=) = flip (<=)

  -- | Strict partial order relation on /a/.
  --
  -- '<' is irreflexive, asymmetric, and transitive.
  --
  -- Furthermore we have:
  --
  -- @
  -- x '<' y ≡ 'maybe' 'False' ('<' 'EQ') ('pcompare' x y)
  -- x '<' y ≡ x '?~' y '==>' x '<=' y '&&' x '\~' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  (<) :: a -> a -> Bool
  x < y = maybe False (P.< EQ) $ pcompare x y

  -- | Converse strict partial order relation on /a/.
  --
  -- '>' is irreflexive, asymmetric, and transitive.
  --
  -- Furthermore we have:
  --
  -- @
  -- x '>' y ≡ 'maybe' 'False' ('>' 'EQ') ('pcompare' x y)
  -- x '>' y ≡ x '?~' y '==>' x '>=' y '&&' x '\~' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  (>) :: Prd a => a -> a -> Bool
  x > y = maybe False (P.> EQ) $ pcompare x y

  -- | Comparability relation on /a/. 
  --
  -- '?~' is reflexive, symmetric, and transitive.
  --
  -- Furthermore we have:
  --
  -- @ 
  -- x '=~' y ≡ 'maybe' 'False' ('const' 'True') ('pcompare' x y)
  -- x '=~' y ≡ x '<=' y '||' x '>=' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  -- If /a/ implements 'Ord' then we must have:
  --
  -- @x '?~' y ≡ 'True'@
  -- for all /x/, /y/ in /a/.
  --
  (?~) :: a -> a -> Bool
  x ?~ y = maybe False (const True) $ pcompare x y

  -- | Equivalence relation on /a/.
  --
  -- '=~' is reflexive, symmetric, and transitive:
  --
  -- Furthermore we have:
  --
  -- @ 
  -- x '=~' y ≡ 'maybe' 'False' ('=~' 'EQ') ('pcompare' x y)
  -- x '=~' y ≡ x '<=' y '&&' x '>=' y
  -- @
  -- for all /x/, /y/ in /a/.
  --
  -- If /a/ implements 'Eq' then it is recommended to use the
  -- same definitions for '==' and '=~'. 
  --
  (=~) :: a -> a -> Bool
  x =~ y = maybe False (== EQ) $ pcompare x y

  -- | Negation of '=~'.
  --
  (/~) :: a -> a -> Bool
  x /~ y = not $ x =~ y

  -- | Similarity relation on /a/. 
  --
  -- '~~' is reflexive and symmetric, but not necessarily transitive.
  --
  -- Furthermore we have:
  --
  -- @ 
  -- x '>=' y ≡ 'maybe' 'True' ('=~' 'EQ') ('pcompare' x y)
  -- x '~~' y ≡ 'not' (x '<' y) '&&' 'not' (x '<' y)
  -- @
  -- for all /x/, /y/ in /a/.
  --
  -- If /a/ implements 'Ord' then we must have:
  --
  -- @x '~~' y ≡ x '=~' y @
  -- for all /x/, /y/ in /a/.
  --
  (~~) :: a -> a -> Bool
  x ~~ y = not (x < y) && not (x > y)

  -- | Negation of '~~'.
  --
  (!~) :: a -> a -> Bool
  x !~ y = not $ x ~~ y

  -- | Partial version of 'compare'. 
  --
  pcompare :: a -> a -> Maybe Ordering
  pcompare x y 
    | x <= y = Just $ if y <= x then EQ else LT
    | y <= x = Just GT
    | otherwise = Nothing


type Bound a = (Minimal a, Maximal a) 

-- | A minimal element of a partially ordered set.
-- 
-- @ 'minimal' '?~' a '==>' 'minimal' '<=' a @
--
-- Note that 'minimal' needn't be comparable to all values in /a/.
--
-- When /a/ is a 'Field' we should have: @ 'minimal' '==' 'ninf' @.
--
-- See < https://en.wikipedia.org/wiki/Maximal_and_minimal_elements >.
--
class Prd a => Minimal a where
    minimal :: a

-- | A maximal element of a partially ordered set.
-- 
-- @ 'maximal' '?~' a '==>' 'maximal' '>=' a @
--
-- Note that 'maximal' needn't be comparable to all values in /a/.
--
-- When /a/ is a 'Semifield' we should have @ 'maximal' = 'pinf' @.
--
-- See < https://en.wikipedia.org/wiki/Maximal_and_minimal_elements >.
--
class Prd a => Maximal a where
    maximal :: a

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

-- | A partial version of ('=~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
peq  :: Prd a => a -> a -> Maybe Bool
peq x y = do
  o <- pcompare x y
  case o of
    EQ -> Just True
    _  -> Just False

-- | A partial version of ('/~')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pne :: Prd a => a -> a -> Maybe Bool
pne x y = do
  o <- pcompare x y
  case o of
    EQ -> Just False
    _  -> Just True

-- | A partial version of ('<=')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
ple :: Prd a => a -> a -> Maybe Bool
ple x y = do
  o <- pcompare x y
  case o of
    GT -> Just False
    _  -> Just True

-- | A partial version of ('>=')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
pge :: Prd a => a -> a -> Maybe Bool
pge x y = do
  o <- pcompare x y
  case o of
    LT -> Just False
    _  -> Just True

-- | A partial version of ('<')  
-- 
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @lt x y == maybe False id $ plt x y@
--
plt :: Prd a => a -> a -> Maybe Bool
plt x y = do
  o <- pcompare x y
  case o of
    LT -> Just True
    _  -> Just False

-- | A partial version of ('>')
--
-- Returns 'Nothing' instead of 'False' when the two values are not comparable.
--
-- @gt x y == maybe False id $ pgt x y@
--
pgt :: Prd a => a -> a -> Maybe Bool
pgt x y = do
  o <- pcompare x y
  case o of
    GT -> Just True
    _  -> Just False

-- | A partial version of 'Data.Ord.max'. 
--
-- Returns the right argument in the case of equality.
--
pmax :: Prd a => a -> a -> Maybe a
pmax x y = do
  o <- pcompare x y
  case o of
    GT -> Just x
    _  -> Just y

-- | A partial version of 'Data.Ord.min'. 
--
-- Returns the right argument in the case of equality.
--
pmin :: Prd a => a -> a -> Maybe a
pmin x y = do
  o <- pcompare x y
  case o of
    GT -> Just y
    _  -> Just x

pabs :: (Additive-Group) a => Prd a => a -> a
pabs x = if zero <= x then x else negate x

sign :: (Additive-Monoid) a => Prd a => a -> Maybe Ordering
sign x = pcompare x zero

finite :: Prd a => Semifield a => a -> Bool
finite = (/~ anan) * (/~ pinf)

finite' :: Prd a => Field a => a -> Bool
finite' = finite * (/~ ninf)

extend :: (Prd a, Semifield a, Semifield b) => (a -> b) -> a -> b
extend f x  | x =~ anan = anan
            | x =~ pinf = pinf
            | otherwise = f x

extend' :: (Prd a, Field a, Field b) => (a -> b) -> a -> b
extend' f x | x =~ ninf = ninf
            | otherwise = extend f x

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

instance Prd a => Prd [a] where
    {-# SPECIALISE instance Prd [Char] #-}
    [] <= _     = True
    (_:_) <= [] = False
    (x:xs) <= (y:ys) = x <= y && xs <= ys

{-
    pcompare []     []     = Just EQ
    pcompare []     (_:_)  = Just LT
    pcompare (_:_)  []     = Just GT
    pcompare (x:xs) (y:ys) = case pcompare x y of
                                Just EQ -> pcompare xs ys
                                other   -> other
-}

instance Prd a => Prd (NonEmpty a) where
    (x :| xs) <= (y :| ys) = x <= y && xs <= ys

instance Prd a => Prd (Down a) where
    (Down x) <= (Down y) = y <= x
    pcompare (Down x) (Down y) = pcompare y x

-- Canonically ordered.
instance Prd a => Prd (Dual a) where
    (Dual x) <= (Dual y) = y <= x
    pcompare (Dual x) (Dual y) = pcompare y x

instance Prd a => Prd (S.Max a) where
    S.Max a <= S.Max b = a <= b

instance Prd a => Prd (S.Min a) where
    S.Min a <= S.Min b = a <= b

instance Prd Any where
    Any x <= Any y = x <= y

instance Prd All where
    All x <= All y = y <= x

instance Prd Float where
    x <= y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = x P.<= y

    x =~ y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = x == y
    
    x ?~ y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = True

    pcompare x y | x /= x && y /= y = Just EQ 
                 | x /= x || y /= y = Nothing
                 | otherwise        = pcompareOrd x y

instance Prd Double where
    x <= y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = x P.<= y

    x =~ y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = x == y

    x ?~ y | x /= x && y /= y = True
           | x /= x || y /= y = False
           | otherwise        = True

    pcompare x y | x /= x && y /= y = Just EQ 
                 | x /= x || y /= y = Nothing
                 | otherwise        = pcompareOrd x y

instance Prd (Ratio Integer) where
    pcompare (x:%y) (x':%y') | (x == 0 && y == 0) && (x' == 0 && y' == 0) = Just EQ
                             | (x == 0 && y == 0) || (x' == 0 && y' == 0) = Nothing
                             | y == 0 && y' == 0 = Just $ compare (signum x) (signum x')
                             | y == 0 = pcompareOrd x 0
                             | y' == 0 = pcompareOrd 0 x'
                             | otherwise = pcompareOrd (x%y) (x'%y')

--TODO add prop tests
instance Prd (Ratio Natural) where
    pcompare (x:%y) (x':%y') | (x == 0 && y == 0) && (x' == 0 && y' == 0) = Just EQ
                             | (x == 0 && y == 0) || (x' == 0 && y' == 0) = Nothing
                             | y == 0 && y' == 0 = Just EQ
                             | y == 0 = Just GT
                             | y' == 0 = Just LT
                             | otherwise = pcompareOrd (x*y') (x'*y)

-- Canonical semigroup ordering
instance Prd a => Prd (Maybe a) where
    Just a <= Just b = a <= b
    Just{} <= Nothing = False
    Nothing <= _ = True

-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (Either a b) where
    Right a <= Right b  = a <= b
    Right _ <= _        = False
    
    Left e <= Left f   = e <= f
    Left _ <= _        = True
 
-- Canonical semigroup ordering
instance (Prd a, Prd b) => Prd (a, b) where 
  (a,b) <= (i,j) = a <= i && b <= j

instance (Prd a, Prd b, Prd c) => Prd (a, b, c) where 
  (a,b,c) <= (i,j,k) = a <= i && b <= j && c <= k

instance (Prd a, Prd b, Prd c, Prd d) => Prd (a, b, c, d) where 
  (a,b,c,d) <= (i,j,k,l) = a <= i && b <= j && c <= k && d <= l

instance (Prd a, Prd b, Prd c, Prd d, Prd e) => Prd (a, b, c, d, e) where 
  (a,b,c,d,e) <= (i,j,k,l,m) = a <= i && b <= j && c <= k && d <= l && e <= m

instance Ord a => Prd (Set.Set a) where
    (<=) = Set.isSubsetOf

instance (Ord k, Prd a) => Prd (Map.Map k a) where
    (<=) = Map.isSubmapOfBy (<=)

instance Prd a => Prd (IntMap.IntMap a) where
    (<=) = IntMap.isSubmapOfBy (<=)

instance Prd IntSet.IntSet where
    (<=) = IntSet.isSubsetOf

#define derivePrd(ty)         \
instance Prd ty where {       \
   (<=) = (P.<=)              \
;  {-# INLINE (<=) #-}        \
;  (>=) = (P.>=)              \
;  {-# INLINE (>=) #-}        \
;  (<)  = (P.<)               \
;  {-# INLINE (<) #-}         \
;  (>)  = (P.>)               \
;  {-# INLINE (>) #-}         \
;  (=~) = (P.==)              \
;  {-# INLINE (=~) #-}        \
;  (~~) = (P.==)              \
;  {-# INLINE (~~) #-}        \
;  pcompare = pcompareOrd     \
;  {-# INLINE pcompare #-}    \
}

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
instance Maximal ty where {          \
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

-------------------------------------------------------------------------------
-- Iterators
-------------------------------------------------------------------------------

{-# INLINE until #-}
until :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
until pre rel f seed = go seed
  where go x | x' `rel` x = x
             | pre x = x
             | otherwise = go x'
          where x' = f x

{-# INLINE while #-}
while :: (a -> Bool) -> (a -> a -> Bool) -> (a -> a) -> a -> a
while pre rel f seed = go seed
  where go x | x' `rel` x = x
             | not (pre x') = x
             | otherwise = go x'
          where x' = f x

-- | Greatest (resp. least) fixed point of a monitone (resp. antitone) function. 
--
-- Does not check that the function is monitone (resp. antitone).
--
-- See also < http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem >.
--
{-# INLINE fixed #-}
fixed :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixed = while (\_ -> True)
