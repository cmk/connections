{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Order (
    -- * Constraint kinds
    Order,
    Total,

    -- * Preorders
    Preorder (..),
    pcomparing,

    -- * DerivingVia
    Base (..),
    N5 (..),

    -- * Re-exports
    Ordering (..),
    Down (..),
    Positive,
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Either
import safe qualified Data.Eq as Eq
import safe Data.Fixed
import safe Data.Functor.Identity
import safe Data.Int
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe Data.List.NonEmpty
import safe qualified Data.Map as Map
import safe Data.Maybe
import safe Data.Ord (Down (..))
import safe qualified Data.Ord as Ord
import safe Data.Semigroup
import safe qualified Data.Set as Set
import safe Data.Void
import safe Data.Word
import safe GHC.Real
import safe Numeric.Natural
import safe Prelude hiding (Bounded, Ord (..), until)

-- | An < https://en.wikipedia.org/wiki/Order_theory#Partially_ordered_sets order > on /a/.
--
-- Note: ideally this would be a subclass of /Preorder/.
--
-- We instead use a constraint kind in order to retain compatibility with the
-- downstream users of /Eq/.
type Order a = (Eq.Eq a, Preorder a)

-- | A < https://en.wikipedia.org/wiki/Total_order total order > on /a/.
--
-- Note: ideally this would be a subclass of /Order/, without instances
-- for /Float/, /Double/, /Rational/, etc.
--
-- We instead use a constraint kind in order to retain compatibility with the
-- downstream users of /Ord/.
type Total a = (Ord.Ord a, Preorder a)

-------------------------------------------------------------------------------
-- Preorders
-------------------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Preorder preorder > on /a/.
--
-- A preorder relation '<~' must satisfy the following two axioms:
--
-- \( \forall x: x \leq x \) (reflexivity)
--
-- \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \) (transitivity)
--
-- Given a preorder on /a/ one may define an equivalence relation '~~' such that
-- /a ~~ b/ if and only if /a <~ b/ and /b <~ a/.
--
-- If no partion induced by '~~' contains more than a single element, then /a/
-- is a partial order and we may define an 'Eq' instance such that the
-- following holds:
--
-- @
-- x '==' y = x '~~' y
-- x '<=' y = x '<' y '||' x '~~' y
-- @
--
-- Minimal complete definition: either 'pcompare' or '<~'. Using 'pcompare' can
-- be more efficient for complex types.
class Preorder a where
    {-# MINIMAL (<~) | pcompare #-}

    infix 4 <~, >~, ?~, ~~, /~, `plt`, `pgt`, `pmax`, `pmin`, `pcompare`

    -- | A non-strict preorder order relation on /a/.
    --
    -- Is /x/ less than or equal to /y/?
    --
    -- '<~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x <~ y = x < y || x ~~ y
    -- > x <~ y = maybe False (<~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    (<~) :: a -> a -> Bool
    x <~ y = maybe False (Ord.<= EQ) (pcompare x y)

    -- | A converse non-strict preorder relation on /a/.
    --
    -- Is /x/ greater than or equal to /y/?
    --
    -- '>~' is reflexive, anti-symmetric, and transitive.
    --
    -- > x >~ y = x > y || x ~~ y
    -- > x >~ y = maybe False (>~ EQ) (pcompare x y)
    --
    -- for all /x/, /y/ in /a/.
    (>~) :: a -> a -> Bool
    (>~) = flip (<~)

    -- | An equivalence relation on /a/.
    --
    -- Are /x/ and /y/ comparable?
    --
    -- '?~' is reflexive, symmetric, and transitive.
    --
    -- If /a/ implements 'Ord' then we should have @x ?~ y = True@.
    (?~) :: a -> a -> Bool
    x ?~ y = maybe False (const True) (pcompare x y)

    -- | An equivalence relation on /a/.
    --
    -- Are /x/ and /y/ equivalent?
    --
    -- '~~' is reflexive, symmetric, and transitive.
    --
    -- > x ~~ y = x <~ y && y <~ x
    -- > x ~~ y = maybe False (~~ EQ) (pcompare x y)
    --
    -- Use this as a lawful substitute for '==' when comparing
    -- floats, doubles, or rationals.
    (~~) :: a -> a -> Bool
    x ~~ y = maybe False (Eq.== EQ) (pcompare x y)

    -- | Negation of '~~'.
    --
    -- Are /x/ and /y/ not equivalent?
    (/~) :: a -> a -> Bool
    x /~ y = not $ x ~~ y

    -- | A strict preorder relation on /a/.
    --
    -- Is /x/ less than /y/?
    --
    -- 'plt' is irreflexive, asymmetric, and transitive.
    --
    -- > x `plt` y = x <~ y && not (y <~ x)
    -- > x `plt` y = maybe False (< EQ) (pcompare x y)
    --
    -- When '<~' is antisymmetric then /a/ is a partial
    -- order and we have:
    --
    -- > x `plt` y = x <~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    plt :: a -> a -> Bool
    plt x y = maybe False (Ord.< EQ) (pcompare x y)

    -- | A converse strict preorder relation on /a/.
    --
    -- Is /x/ greater than /y/?
    --
    -- 'pgt' is irreflexive, asymmetric, and transitive.
    --
    -- > x `pgt` y = x >~ y && not (y >~ x)
    -- > x `pgt` y = maybe False (> EQ) (pcompare x y)
    --
    -- When '<~' is antisymmetric then /a/ is a partial
    -- order and we have:
    --
    -- > x `pgt` y = x >~ y && x /~ y
    --
    -- for all /x/, /y/ in /a/.
    pgt :: a -> a -> Bool
    pgt = flip plt

    -- | A similarity relation on /a/.
    --
    -- Are /x/ and /y/ either equivalent or incomparable?
    --
    -- 'similar' is reflexive and symmetric, but not necessarily transitive.
    --
    -- Note this is only equivalent to '==' in a total order:
    --
    -- > similar (0/0 :: Float) 5 = True
    --
    -- If /a/ implements 'Ord' then we should have @('~~') = 'similar' = ('==')@.
    similar :: a -> a -> Bool
    similar x y = maybe True (Eq.== EQ) (pcompare x y)

    -- | A partial version of 'Data.Ord.max'.
    --
    -- Returns the left-hand argument in the case of equality.
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
    pmin :: a -> a -> Maybe a
    pmin x y = do
        o <- pcompare x y
        case o of
            GT -> Just y
            EQ -> Just x
            LT -> Just x

    -- | A partial version of 'Data.Ord.compare'.
    --
    -- > x <  y = maybe False (<  EQ) $ pcompare x y
    -- > x >  y = maybe False (>  EQ) $ pcompare x y
    -- > x <~ y = maybe False (<~ EQ) $ pcompare x y
    -- > x >~ y = maybe False (>~ EQ) $ pcompare x y
    -- > x ~~ y = maybe False (~~ EQ) $ pcompare x y
    -- > x ?~ y = maybe False (const True) $ pcompare x y
    -- > similar x y = maybe True (~~ EQ) $ pcompare x y
    --
    -- If /a/ implements 'Ord' then we should have @'pcompare' x y = 'Just' '$' 'compare' x y@.
    pcompare :: a -> a -> Maybe Ordering
    pcompare x y
        | x <~ y = Just $ if y <~ x then EQ else LT
        | y <~ x = Just GT
        | otherwise = Nothing

-- | A partial version of 'Data.Order.Total.comparing'.
--
-- > pcomparing p x y = pcompare (p x) (p y)
--
-- The partial application /pcomparing f/ induces a lawful preorder for
-- any total function /f/.
pcomparing :: Preorder a => (b -> a) -> b -> b -> Maybe Ordering
pcomparing p x y = pcompare (p x) (p y)

---------------------------------------------------------------------
-- DerivingVia
---------------------------------------------------------------------

newtype Base a = Base {getBase :: a}
    deriving stock (Eq.Eq, Ord.Ord, Show, Functor)
    deriving (Applicative) via Identity

instance Ord.Ord a => Preorder (Base a) where
    x <~ y = getBase $ liftA2 (Ord.<=) x y
    x >~ y = getBase $ liftA2 (Ord.>=) x y
    pcompare x y = Just . getBase $ liftA2 Ord.compare x y

--instance Preorder Void where  _ <~ _ = True
deriving via (Base Void) instance Preorder Void
deriving via (Base ()) instance Preorder ()
deriving via (Base Bool) instance Preorder Bool
deriving via (Base Ordering) instance Preorder Ordering
deriving via (Base Char) instance Preorder Char
deriving via (Base Word) instance Preorder Word
deriving via (Base Word8) instance Preorder Word8
deriving via (Base Word16) instance Preorder Word16
deriving via (Base Word32) instance Preorder Word32
deriving via (Base Word64) instance Preorder Word64
deriving via (Base Natural) instance Preorder Natural
deriving via (Base Int) instance Preorder Int
deriving via (Base Int8) instance Preorder Int8
deriving via (Base Int16) instance Preorder Int16
deriving via (Base Int32) instance Preorder Int32
deriving via (Base Int64) instance Preorder Int64
deriving via (Base Integer) instance Preorder Integer

deriving via (Base (Fixed e)) instance Preorder (Fixed e)

-- | An < https://en.wikipedia.org/wiki/Modular_lattice#Examples /N5/ > lattice.
--
--  A non-modular lattice formed by the < https://en.wikipedia.org/wiki/Extended_real_number_line affine extended >
--  reals along with a /NaN/ value that is incomparable to any finite number, i.e.:
--
--  > pcompare (N5 NaN) (N5 x) = pcompare (N5 x) (N5 NaN) = Nothing
--
--  for any finite /x/.
--
--  > N5 NaN == N5 NaN = True
--  > N5 NaN < N5 (1/0) = True
--  > N5 NaN > N5 (-1/0) = True
newtype N5 a = N5 {getN5 :: a}
    deriving stock (Eq, Show, Functor)
    deriving (Applicative) via Identity

instance (Ord.Ord a, Fractional a) => Preorder (N5 a) where
    x <~ y = getN5 $ liftA2 n5Le x y

-- N5 lattice ordering: NInf <= NaN <= PInf
n5Le :: (Ord.Ord a, Fractional a) => a -> a -> Bool
n5Le x y
    | x Eq./= x && y Eq./= y = True
    | x Eq./= x = y == 1 / 0
    | y Eq./= y = x == -1 / 0
    | otherwise = x Ord.<= y

deriving via (N5 Float) instance Preorder Float
deriving via (N5 Double) instance Preorder Double

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- N5 lattice ordering: NInf <= NaN <= PInf
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
pcompareRat :: Rational -> Rational -> Maybe Ordering
pcompareRat (0 :% 0) (x :% 0) = Just $ Ord.compare 0 x
pcompareRat (x :% 0) (0 :% 0) = Just $ Ord.compare x 0
pcompareRat (x :% 0) (y :% 0) = Just $ Ord.compare (signum x) (signum y)
pcompareRat (0 :% 0) _ = Nothing
pcompareRat _ (0 :% 0) = Nothing
pcompareRat _ (x :% 0) = Just $ Ord.compare 0 x -- guard against div-by-zero exceptions
pcompareRat (x :% 0) _ = Just $ Ord.compare x 0
pcompareRat x y = Just $ Ord.compare x y

-- | Positive rationals, extended with an absorbing zero.
--
-- 'Positive' is the canonical < https://en.wikipedia.org/wiki/Semifield#Examples semifield >.
type Positive = Ratio Natural

-- N5 lattice comparison
pcomparePos :: Positive -> Positive -> Maybe Ordering
pcomparePos (0 :% 0) (x :% 0) = Just $ Ord.compare 0 x
pcomparePos (x :% 0) (0 :% 0) = Just $ Ord.compare x 0
pcomparePos (_ :% 0) (_ :% 0) = Just EQ -- all non-nan infs are equal
pcomparePos (0 :% 0) (0 :% _) = Just $ GT
pcomparePos (0 :% _) (0 :% 0) = Just $ LT
pcomparePos (0 :% 0) _ = Nothing
pcomparePos _ (0 :% 0) = Nothing
pcomparePos (x :% y) (x' :% y') = Just $ Ord.compare (x * y') (x' * y)

instance Preorder Rational where
    pcompare = pcompareRat

instance Preorder Positive where
    pcompare = pcomparePos

instance (Preorder a, Num a) => Preorder (Complex a) where
    pcompare = pcomparing $ \(x :+ y) -> x * x + y * y

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

instance Preorder a => Preorder (Identity a) where
    pcompare (Identity x) (Identity y) = pcompare x y

instance Preorder a => Preorder (Maybe a) where
    Nothing <~ _ = True
    Just{} <~ Nothing = False
    Just a <~ Just b = a <~ b

instance Preorder a => Preorder [a] where
    {-# SPECIALIZE instance Preorder [Char] #-}

    --[] <~ _     = True
    --(_:_) <~ [] = False
    --(x:xs) <~ (y:ys) = x <~ y && xs <~ ys

    pcompare [] [] = Just EQ
    pcompare [] (_ : _) = Just LT
    pcompare (_ : _) [] = Just GT
    pcompare (x : xs) (y : ys) = case pcompare x y of
        Just EQ -> pcompare xs ys
        other -> other

instance Preorder a => Preorder (NonEmpty a) where
    (x :| xs) <~ (y :| ys) = x <~ y && xs <~ ys

instance (Preorder a, Preorder b) => Preorder (Either a b) where
    Right a <~ Right b = a <~ b
    Right _ <~ _ = False
    Left a <~ Left b = a <~ b
    Left _ <~ _ = True

instance (Preorder a, Preorder b) => Preorder (a, b) where
    (a, b) <~ (i, j) = a <~ i && b <~ j

instance (Preorder a, Preorder b, Preorder c) => Preorder (a, b, c) where
    (a, b, c) <~ (i, j, k) = a <~ i && b <~ j && c <~ k

instance (Preorder a, Preorder b, Preorder c, Preorder d) => Preorder (a, b, c, d) where
    (a, b, c, d) <~ (i, j, k, l) = a <~ i && b <~ j && c <~ k && d <~ l

instance (Preorder a, Preorder b, Preorder c, Preorder d, Preorder e) => Preorder (a, b, c, d, e) where
    (a, b, c, d, e) <~ (i, j, k, l, m) = a <~ i && b <~ j && c <~ k && d <~ l && e <~ m

instance (Ord.Ord k, Preorder a) => Preorder (Map.Map k a) where
    (<~) = Map.isSubmapOfBy (<~)

instance Ord.Ord a => Preorder (Set.Set a) where
    (<~) = Set.isSubsetOf

instance Preorder a => Preorder (IntMap.IntMap a) where
    (<~) = IntMap.isSubmapOfBy (<~)

instance Preorder IntSet.IntSet where
    (<~) = IntSet.isSubsetOf
