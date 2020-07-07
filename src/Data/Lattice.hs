{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeOperators              #-}
-- | Lattices & algebras
module Data.Lattice (
  -- * Types
    Lattice
  , Semilattice
  -- * HeytingL
  , type HeytingL
  , (\\)
  , non
  , equiv
  , boundary
  , booleanL
  , heytingL
  -- * HeytingR
  , type HeytingR
  , (//)
  , neg
  , iff
  , middle
  , booleanR
  , heytingR
  -- * Heyting
  , (\/)
  , (/\)
  , glb
  , lub
  , true
  , false
  , Heyting(..)
  -- * Symmetric
  , Biheyting
  , Symmetric(..)
  , symmetricL
  , symmetricR
  -- * Boolean
  , Boolean(..)
) where

import safe Control.Applicative
import safe Data.Bifunctor (bimap)
import safe Data.Bool hiding (not)
import safe Data.Connection.Conn
import safe Data.Connection.Class
import safe Data.Either
import safe Data.Functor.Contravariant
import safe Data.Foldable
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Interval
import safe Data.Order.Syntax
import safe Data.Int
import safe Data.Maybe
import safe Data.Monoid
import safe Data.Word
import safe GHC.TypeNats
--import safe Numeric.Natural
import safe Prelude hiding (Eq(..),Ord(..),Bounded, not)
import safe qualified Data.IntMap as IntMap
import safe qualified Data.IntSet as IntSet
import safe qualified Data.Map as Map
import safe qualified Data.Map.Merge.Lazy as Map
import safe qualified Data.Set as Set
import safe qualified Data.Finite as F
import safe qualified Data.Universe.Class as U
import safe qualified Prelude as P

-------------------------------------------------------------------------------
-- Lattices
-------------------------------------------------------------------------------

-- | Bounded < https://ncatlab.org/nlab/show/lattice lattices >.
--
-- /Neutrality/:
--
-- The least and greatest elements of a complete /a/ are given by the unique
-- upper and lower adjoints to the function /a -> ()/.
--
-- @
-- x '\/' 'false' = x
-- x '/\' 'true' = x
-- 'glb' 'false' x 'true' = x
-- 'lub' 'false' x 'true' = x
-- @
--
type Lattice a = (Eq a, Semilattice 'L a, Extremal 'L a, Semilattice 'R a, Extremal 'R a)

-- | The unique top element of a bounded lattice
--
-- > x /\ true = x
-- > x \/ true = true
--
true :: Lattice a => a
true = maximal

-- | The unique bottom element of a bounded lattice
--
-- > x /\ false = false
-- > x \/ false = x
--
false :: Lattice a => a
false = minimal

-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

-- | A < https://ncatlab.org/nlab/show/co-Heyting+algebra bi-Heyting algebra >.
--
-- /Laws/:
--
-- > neg x <= non x
--
-- with equality occurring iff /a/ is a 'Boolean' algebra.
--
type Biheyting a = (HeytingL a, HeytingR a)

-- | A convenience alias for a < https://ncatlab.org/nlab/show/co-Heyting+algebra co-Heyting algebra >.
--
type HeytingL = Heyting 'L

-- | A convenience alias for a Heyting algebra.
--
type HeytingR = Heyting 'R

-- | Heyting algebras
--
-- A Heyting algebra is a bounded, distributive complete equipped with an
-- implication operation.
--
-- * The complete of closed subsets of a trueological space is the primordial
-- example of a /HeytingL/ (co-Heyting) algebra.
--
-- * The dual complete of open subsets of a trueological space is likewise
-- the primordial example of a /HeytingR/ algebra.
--
-- /Heyting 'L/:
-- 
-- Co-implication to /a/ is the lower adjoint of disjunction with /a/:
--
-- > x \\ a <= y <=> x <= y \/ a
--
-- Note that co-Heyting algebras needn't obey the law of non-contradiction:
--
-- > EQ /\ non EQ = EQ /\ GT \\ EQ = EQ /\ GT = EQ /= LT
--
-- See < https://ncatlab.org/nlab/show/co-Heyting+algebra >
--
-- /Heyting 'R/:
--
-- Implication from /a/ is the upper adjoint of conjunction with /a/:
-- 
-- > x <= a // y <=> a /\ x <= y
--
-- Similarly, Heyting algebras needn't obey the law of the excluded middle:
--
-- > EQ \/ neg EQ = EQ \/ EQ // LT = EQ \/ LT = EQ /= GT
--
-- See < https://ncatlab.org/nlab/show/Heyting+algebra >
--
class Lattice a => Heyting k a where
    
    -- | The defining connection of a (co-)Heyting algebra.
    --
    -- > heyting @'L x = ConnL (\\ x) (\/ x) 
    -- > heyting @'R x = ConnR (x /\) (x //)
    --
    heyting :: a -> Conn k a a

-------------------------------------------------------------------------------
-- HeytingL
-------------------------------------------------------------------------------

infixl 8 \\

-- | Logical co-implication:
--
-- \( a \Rightarrow b = \wedge \{x \mid a \leq b \vee x \} \)
--
-- /Laws/:
-- 
-- > x \\ y <= z <=> x <= y \/ z
-- > x \\ y >= (x /\ z) \\ y
-- > x >= y => x \\ z >= y \\ z
-- > x >= x \\ y
-- > x >= y <=> y \\ x = false
-- > x \\ (y /\ z) >= x \\ y
-- > z \\ (x \/ y) = z \\ x \\ y
-- > (y \/ z) \\ x = y \\ x \/ z \\ x
-- > x \/ y \\ x = x \/ y
--
-- >>> False \\ False
-- False
-- >>> False \\ True
-- False
-- >>> True \\ False
-- True
-- >>> True \\ True
-- False
--
-- For many collections (e.g. 'Data.Set.Set') '\\' coincides with the native 'Data.Set.\\' operator.
--
-- >>> :set -XOverloadedLists
-- >>> [GT,EQ] Set.\\ [LT]
-- fromList [EQ,GT]
-- >>> [GT,EQ] \\ [LT]
-- fromList [EQ,GT]
-- 
(\\) :: Heyting 'L a => a -> a -> a
(\\) = flip $ lowerL . heyting

-- | Logical < https://ncatlab.org/nlab/show/co-Heyting+negation co-negation >.
--
-- @ 'non' x = 'true' '\\' x @
--
-- /Laws/:
-- 
-- > non false = true
-- > non true = false
-- > x >= non (non x)
-- > non (x /\ y) >= non x
-- > non (y \\ x) = non (non x) \/ non y
-- > non (x /\ y) = non x \/ non y
-- > x \/ non x = true
-- > non (non (non x)) = non x
-- > non (non (x /\ non x)) = false
--
non :: Heyting 'L a => a -> a
non x = true \\ x

-- | Intuitionistic co-equivalence.
--
equiv :: Heyting 'L a => a -> a -> a
equiv x y = (x \\ y) \/ (y \\ x)

-- | The co-Heyting < https://ncatlab.org/nlab/show/co-Heyting+boundary boundary > operator.    
--
-- > x = boundary x \/ (non . non) x
-- > boundary (x /\ y) = (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)
-- > boundary (x \/ y) \/ boundary (x /\ y) = boundary x \/ boundary y
--
boundary :: Heyting 'L a => a -> a
boundary x = x /\ non x

-- | An adjunction between a co-Heyting algebra and its Boolean sub-algebra.
--
-- Double negation is a join-preserving comonad.
--
booleanL :: Heyting 'L a => Conn 'L a a
booleanL =
  let 
    -- Check that /x/ is a regular element
    -- See https://ncatlab.org/nlab/show/regular+element
    inj x = if x == (non . non) x then x else true

  in
    ConnL inj (non . non)

-- | Default constructor for a co-Heyting algebra.
--
heytingL :: Lattice a => (a -> a -> a) -> a -> Conn 'L a a
heytingL f a = ConnL (`f` a) (\/ a)

-------------------------------------------------------------------------------
-- HeytingR
-------------------------------------------------------------------------------

infixr 8 // -- same as ^

-- | Logical implication:
--
-- \( a \Rightarrow b = \vee \{x \mid x \wedge a \leq b \} \)
--
-- /Laws/:
--
-- > x /\ y <= z <=> x <= y // z
-- > x // y <= x // (y \/ z)
-- > x <= y => z // x <= z // y
-- > y <= x // (x /\ y)
-- > x <= y <=> x // y = true
-- > (x \/ z) // y <= x // y
-- > (x /\ y) // z = x // y // z
-- > x // (y /\ z) = x // y /\ x // z
-- > x /\ x // y = x /\ y
--
-- >>> False // False
-- True
-- >>> False // True
-- True
-- >>> True // False
-- False
-- >>> True // True
-- True
--
(//) :: Heyting 'R a => a -> a -> a
(//) x = upperR $ heyting x

-- | Logical negation.
--
-- @ 'neg' x = x '//' 'false' @
--
-- /Laws/:
--
-- > neg false = true
-- > neg true = false
-- > x <= neg (neg x)
-- > neg (x \/ y) <= neg x
-- > neg (x // y) = neg (neg x) /\ neg y
-- > neg (x \/ y) = neg x /\ neg y
-- > x /\ neg x = false
-- > neg (neg (neg x)) = neg x
-- > neg (neg (x \/ neg x)) = true
--
-- Some logics may in addition obey < https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra De Morgan conditions >.
--
neg :: Heyting 'R a => a -> a
neg x = x // false

-- | Intuitionistic equivalence.
--
-- When /a=Bool/ this is 'if-and-only-if'.
--
iff :: Heyting 'R a => a -> a -> a
iff x y = (x // y) /\ (y // x)

-- | The Heyting (< https://ncatlab.org/nlab/show/excluded+middle not necessarily excluded>) middle operator.
--
middle :: Heyting 'R a => a -> a
middle x = x \/ neg x

-- | An adjunction between a Heyting algebra and its Boolean sub-algebra.
--
-- Double negation is a meet-preserving monad.
--
booleanR :: Heyting 'R a => Conn 'R a a
booleanR = 
  let
    -- Check that /x/ is a regular element
    -- See https://ncatlab.org/nlab/show/regular+element
    inj x = if x == (neg . neg) x then x else false

  in 
    ConnR (neg . neg) inj

-- | Default constructor for a Heyting algebra.
--
heytingR :: Lattice a => (a -> a -> a) -> a -> Conn 'R a a
heytingR f a = ConnR (a /\) (a `f`)

-------------------------------------------------------------------------------
-- Symmetric
-------------------------------------------------------------------------------

-- | Symmetric Heyting algebras
--
-- A symmetric Heyting algebra is a <https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra De Morgan >
-- bi-Heyting algebra with an idempotent, antitone negation operator.
--
-- /Laws/:
--
-- > x <= y => not y <= not x -- antitone
-- > not . not = id           -- idempotence
-- > x \\ y = not (not y // not x)
-- > x // y = not (not y \\ not x)
--
-- and:
--
-- > converseR x <= converseL x
--
-- with equality occurring iff /a/ is a 'Boolean' algebra.
--
class Biheyting a => Symmetric a where

    -- | Symmetric negation.
    --
    -- > not . not = id
    -- > neg . neg = converseR . converseL
    -- > non . non = converseL . converseR
    -- > neg . non = converseR . converseR
    -- > non . neg = converseL . converseL
    --
    -- > neg = converseR . not = not . converseL
    -- > non = not . converseR = converseL . not
    -- > x \\ y = not (not y // not x)
    -- > x // y = not (not y \\ not x)
    --
    not :: a -> a

    infixl 4 `xor`

    -- | Exclusive or.
    --
    -- > xor x y = (x \/ y) /\ (not x \/ not y)
    --
    xor :: a -> a -> a
    xor x y = (x \/ y) /\ not (x /\ y)

    -- | Left converse operator.
    --    
    converseL :: a -> a
    converseL x = true \\ not x

    -- | Right converse operator.
    --    
    converseR :: a -> a
    converseR x = not x // false

-- | Default constructor for a co-Heyting algebra.
--
symmetricL :: Symmetric a => a -> ConnL a a
symmetricL = heytingL $ \x y -> not (not y // not x)

-- | Default constructor for a Heyting algebra.
--
symmetricR :: Symmetric a => a -> ConnR a a
symmetricR = heytingR $ \x y -> not (not y \\ not x)

-------------------------------------------------------------------------------
-- Boolean
-------------------------------------------------------------------------------

-- | Boolean algebras.
--
-- < https://ncatlab.org/nlab/show/Boolean+algebra Boolean algebras > are 
-- symmetric Heyting algebras that satisfy both the law of excluded middle
-- and the law of law of non-contradiction:
--
-- > x \/ neg x = true
-- > x /\ non x = false
--
-- If /a/ is Boolean we also have:
--
-- > non = not = neg
--
class Symmetric a => Boolean a where

    -- | A witness to the lawfulness of a boolean algebra.
    --
    boolean :: Trip a a
    boolean = Conn (converseR . converseL) id (converseL . converseR)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


impliesL :: (Total a, P.Bounded a) => a -> a -> a
impliesL x y = if y < x then x else P.minBound

impliesR :: (Total a, P.Bounded a) => a -> a -> a
impliesR x y = if x > y then y else P.maxBound

instance Heyting 'L () where heyting = heytingL impliesL
instance Heyting 'L Bool where heyting = heytingL impliesL
instance Heyting 'L Ordering where heyting = heytingL impliesL
instance Heyting 'L Word8 where heyting = heytingL impliesL
instance Heyting 'L Word16 where heyting = heytingL impliesL
instance Heyting 'L Word32 where heyting = heytingL impliesL
instance Heyting 'L Word64 where heyting = heytingL impliesL
instance Heyting 'L Word where heyting = heytingL impliesL
instance KnownNat n => Heyting 'L (F.Finite n) where heyting = heytingL impliesL

instance Heyting 'R () where heyting = heytingR impliesR
instance Heyting 'R Bool where heyting = heytingR impliesR
--instance Heyting 'R Ordering where heyting = heytingR impliesR
instance Heyting 'R Word8 where heyting = heytingR impliesR
instance Heyting 'R Word16 where heyting = heytingR impliesR
instance Heyting 'R Word32 where heyting = heytingR impliesR
instance Heyting 'R Word64 where heyting = heytingR impliesR
instance Heyting 'R Word where heyting = heytingR impliesR
instance KnownNat n => Heyting 'R (F.Finite n) where heyting = heytingR impliesR

instance Heyting 'L Int8 where heyting = heytingL impliesL
instance Heyting 'L Int16 where heyting = heytingL impliesL
instance Heyting 'L Int32 where heyting = heytingL impliesL
instance Heyting 'L Int64 where heyting = heytingL impliesL
instance Heyting 'L Int where heyting = heytingL impliesL
instance Heyting 'R Int8 where heyting = heytingR impliesR
instance Heyting 'R Int16 where heyting = heytingR impliesR
instance Heyting 'R Int32 where heyting = heytingR impliesR
instance Heyting 'R Int64 where heyting = heytingR impliesR
instance Heyting 'R Int where heyting = heytingR impliesR

instance Symmetric () where not _ = ()
instance Symmetric Bool where not = P.not
instance Symmetric Ordering where
  not LT = GT
  not EQ = EQ
  not GT = LT
 
instance Heyting 'R Ordering where heyting = symmetricR

instance Boolean ()
instance Boolean Bool

-------------------------------------------------------------------------------
-- Instances: sum types
-------------------------------------------------------------------------------



-- |
-- Subdirectly irreducible Heyting algebra.
instance Heyting 'R a => Heyting 'R (Lowered a) where
  heyting = heytingR f where

    (Left a)  `f` (Left b) | a <= b    = true
                           | otherwise = Left (a // b)
    (Right _) `f` a                    = a
    _         `f` (Right _)            = true

instance Heyting 'R a => Heyting 'R (Lifted a) where
  heyting = heytingR f where
    f (Right a) (Right b) = Right (a // b)
    f (Left _)   _        = Right true
    f _         (Left _)  = false

instance Heyting 'R a => Heyting 'R (Maybe a) where
  heyting = heytingR f where
    f (Just a) (Just b)   = Just (a // b)
    f Nothing  _          = Just true
    f _        Nothing    = Nothing

--instance Complete k a => Complete k (Extended a)
instance Heyting 'R a => Heyting 'R (Extended a) where
  heyting = heytingR f where

    Extended a `f` Extended b | a <= b    = Top
                              | otherwise = Extended (a // b)
    Top        `f` a          = a
    _          `f` Top        = Top
    Bottom     `f` _          = Top
    _          `f` Bottom     = Bottom

--instance Symmetric a => Symmetric (Extended a) where

-------------------------------------------------------------------------------
-- Instances: product types
-------------------------------------------------------------------------------

instance (Heyting k a, Heyting k b) => Heyting k (a, b) where
  heyting (a,b) = heyting a `strong` heyting b

instance (Symmetric a, Symmetric b) => Symmetric (a, b) where
  not = bimap not not

instance (Boolean a, Boolean b) => Boolean (a, b) where

-------------------------------------------------------------------------------
-- Instances: function types
-------------------------------------------------------------------------------


instance (U.Finite a, Biheyting b) => Heyting 'L (a -> b) where
  heyting = heytingL $ liftA2 (\\)

instance (U.Finite a, Biheyting b) => Heyting 'R (a -> b) where
  heyting = heytingR $ liftA2 (//)

instance (U.Finite a, Symmetric b) => Symmetric (a -> b) where not = fmap not

instance (U.Finite a, Boolean b) => Boolean (a -> b)

deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'L (Endo a)
deriving via (a -> a) instance (U.Finite a, Biheyting a) => Heyting 'R (Endo a)
instance (U.Finite a, Symmetric a) => Symmetric (Endo a)
instance (U.Finite a, Boolean a) => Boolean (Endo a)

deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'L (Op b a)
deriving via (a -> b) instance (U.Finite a, Biheyting b) => Heyting 'R (Op b a)
instance (U.Finite a, Symmetric b) => Symmetric (Op b a)
instance (U.Finite a, Boolean b) => Boolean (Op b a)

deriving via (Op Bool a) instance (U.Finite a) => Heyting 'L (Predicate a)
deriving via (Op Bool a) instance (U.Finite a) => Heyting 'R (Predicate a)
instance (U.Finite a) => Symmetric (Predicate a)
instance (U.Finite a) => Boolean (Predicate a)

-------------------------------------------------------------------------------
-- Instances: collections
-------------------------------------------------------------------------------


instance (Total a, U.Finite a) => Heyting 'L (Set.Set a) where
  heyting = heytingL (Set.\\)

instance (Total a, U.Finite a) => Heyting 'R (Set.Set a) where
  heyting = symmetricR

instance (Total a, U.Finite a) => Symmetric (Set.Set a) where
  not = non --(U.universe Set.\\)

instance (Total a, U.Finite a) => Boolean (Set.Set a) where

instance Heyting 'L IntSet.IntSet where
  heyting = heytingL (IntSet.\\)

instance Heyting 'R IntSet.IntSet where
  --heyting = heytingR $ \x y -> non x \/ y
  heyting = symmetricR

instance Symmetric IntSet.IntSet where
  not = non --(U.universe IntSet.\\)

instance Boolean IntSet.IntSet where

{- TODO pick an instance either key-aware or no
instance (Total a, U.Finite a, Lattice b) => Heyting 'L (Map.Map a b) where
  heyting = heytingL (Map.\\)

instance (Total a, U.Finite a, Heyting 'R b) => Heyting 'R (Map.Map a b) where

  heyting = heytingR $ \a b ->
    let
      x = Map.merge
            Map.dropMissing                    -- drop if an element is missing in @b@
            (Map.mapMissing (\_ _ -> true))     -- put @true@ if an element is missing in @a@
            (Map.zipWithMatched (\_ -> (//) )) -- merge  matching elements with @`implies`@
            a b

      y = Map.fromList [(k, true) | k <- U.universeF, not (Map.member k a), not (Map.member k b) ]
        -- for elements which are not in a, nor in b add
        -- a @true@ key
    in
      Map.union x y
{-
-- TODO: compare performance
impliesMap a b =
  Map.intersection (`implies`) a b
    `Map.union` Map.map (const true) (Map.difference b a)
    `Map.union` Map.fromList [(k, true) | k <- universeF, not (Map.member k a), not (Map.member k b)]
-}
-}


{-

-- A symmetric Heyting algebra
-- 
-- λ> implies (False ... True) (False ... True)
-- Interval True True
-- λ> implies (False ... True) (singleton False)
-- Interval False False
-- λ> implies (singleton True) (False ... True)
-- Interval False True
-- 
-- λ> implies ([EQ,GT] ... [EQ,GT]) ([LT] ... [LT,EQ])  :: Interval (Set.Set Ordering)
-- Interval (fromList [LT]) (fromList [LT,EQ])
-- 
-- TODO: may need /a/ to be boolean here.
implies :: Symmetric a => Interval a -> Interval a -> Interval a
implies i1 i2 = maybe iempty (uncurry (...)) $ liftA2 f (endpts i1) (endpts i2) where
  f (x1,x2) (y1,y2) = (x1 // y1 /\ x2 // y2, x2 // y2)

  --TODO: would this work for interval orders?
  f (x1,x2) (y1,y2) = (x1 // y1 /\ x2 // y2, x1 // y1 \/ x2 // y2)

coimplies i1 i2 = not (not i1 `implies` not i2)

-- The symmetry
-- neg x = true \\ not x
-- non x = not x // false
-- λ> not ([LT] ... [LT,GT]) :: Interval (Set.Set Ordering)
-- Interval (fromList [EQ]) (fromList [EQ,GT])
-- 
not :: Symmetric a => Interval a -> Interval a
not = maybe iempty (\(x1, x2) -> neg x2 ... neg x1) . endpts

-- λ> neg' (False ... True)
-- Interval False False
-- λ> (False ... True) `implies` (singleton False)
-- Interval False False
-- 
neg' x = (false ... true) `coimplies` (not x)

-- λ> non' (False ... True)
-- Interval False False
-- λ> (singleton True) `coimplies` (False ... True)
-- Interval False False
-- 
non' x = not x `implies` (singleton false)

-}


