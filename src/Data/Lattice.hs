{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Lattices & algebras
module Data.Lattice (
    -- * Semilattice
    Lattice,
    Semilattice (..),

    -- ** Meet
    Meet,
    (/\),
    glb,
    top,

    -- ** Join
    Join,
    (\/),
    lub,
    bottom,

    -- * Algebra
    Biheyting,
    Algebra (..),

    -- ** Heyting
    Heyting,
    (//),
    iff,
    neg,
    middle,
    heyting,
    booleanR,

    -- ** Coheyting
    Coheyting,
    (\\),
    equiv,
    non,
    boundary,
    coheyting,
    booleanL,

    -- ** Symmetric
    Symmetric (..),
    converseL,
    converseR,
    symmetricL,
    symmetricR,

    -- ** Boolean
    Boolean (..),
) where

import Data.Bifunctor (bimap)
import Data.Bool hiding (not)
import Data.Connection.Cast
import Data.Either
import Data.Int
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Order
import Data.Order.Syntax
import qualified Data.Set as Set
import Data.Word
import Prelude hiding (Eq (..), Ord (..), ceiling, floor, not)
import qualified Prelude as P

-- >>> import Data.IntSet (IntSet,fromList)
-- >>> :load Data.Connection
-- >>> import Prelude hiding (round, floor, ceiling, truncate)

-------------------------------------------------------------------------------
-- Lattices
-------------------------------------------------------------------------------

type Lattice a = (Join a, Meet a)

-- | A convenience alias for a join semilattice
type Join = Semilattice 'L

-- | A convenience alias for a meet semilattice
type Meet = Semilattice 'R

-- | Bounded < https://ncatlab.org/nlab/show/lattice lattices >.
--
-- A lattice is a partially ordered set in which every two elements have a unique join
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum).
--
-- A bound lattice adds unique elements 'top' and 'bottom', which serve as
-- identities to '\/' and '/\', respectively.
--
-- /Neutrality/:
--
-- @
-- x '\/' 'bottom' = x
-- x '/\' 'top' = x
-- 'glb' 'bottom' x 'top' = x
-- 'lub' 'bottom' x 'top' = x
-- @
--
-- /Associativity/
--
-- @
-- x '\/' (y '\/' z) = (x '\/' y) '\/' z
-- x '/\' (y '/\' z) = (x '/\' y) '/\' z
-- @
--
-- /Commutativity/
--
-- @
-- x '\/' y = y '\/' x
-- x '/\' y = y '/\' x
-- @
--
-- /Idempotency/
--
-- @
-- x '\/' x = x
-- x '/\' x = x
-- @
--
-- /Absorption/
--
-- @
-- (x '\/' y) '/\' y = y
-- (x '/\' y) '\/' y = y
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law Absorption >.
--
-- Note that distributivity is _not_ a requirement for a complete.
-- However when /a/ is distributive we have:
--
-- @
-- 'glb' x y z = 'lub' x y z
-- @
--
-- See < https://en.wikipedia.org/wiki/Lattice_(order) >.
class Order a => Semilattice k a where
    -- | The defining connection of a bound semilattice.
    --
    -- 'bottom' and 'top' are defined by the left and right adjoints to /a -> ()/.
    bound :: Cast k () a

    -- | The defining connection of a semilattice.
    --
    -- '\/' and '/\' are defined by the left and right adjoints to /a -> (a, a)/.
    semilattice :: Cast k (a, a) a

infixr 6 /\ -- comment for the parser

-- | Lattice meet.
--
-- > (/\) = curry $ floor semilattice
(/\) :: Meet a => a -> a -> a
(/\) = curry $ floor semilattice

-- | Greatest lower bound operator.
--
-- > glb x x y = x
-- > glb x y z = glb z x y
-- > glb x y z = glb x z y
-- > glb (glb x w y) w z = glb x w (glb y w z)
--
-- >>> glb 1.0 9.0 7.0
-- 7.0
-- >>> glb 1.0 9.0 (0.0 / 0.0)
-- 9.0
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: IntSet
-- fromList [3,5]
glb :: Lattice a => a -> a -> a -> a
glb x y z = (x \/ y) /\ (y \/ z) /\ (z \/ x)

-- | The unique top element of a bound lattice
--
-- > x /\ top = x
-- > x \/ top = top
top :: Meet a => a
top = floor bound ()

infixr 5 \/

-- | Lattice join.
--
-- > (\/) = curry $ lower semilattice
(\/) :: Join a => a -> a -> a
(\/) = curry $ ceiling semilattice

-- | Least upper bound operator.
--
-- The order dual of 'glb'.
--
-- >>> lub 1.0 9.0 7.0
-- 7.0
-- >>> lub 1.0 9.0 (0.0 / 0.0)
-- 1.0
lub :: Lattice a => a -> a -> a -> a
lub x y z = x /\ y \/ y /\ z \/ z /\ x

-- | The unique bottom element of a bound lattice
--
-- > x /\ bottom = bottom
-- > x \/ bottom = x
bottom :: Join a => a
bottom = ceiling bound ()

-------------------------------------------------------------------------------
-- Heyting algebras
-------------------------------------------------------------------------------

-- | A convenience alias for a Heyting algebra.
type Heyting a = (Lattice a, Algebra 'R a)

-- | A convenience alias for a < https://ncatlab.org/nlab/show/co-Heyting+algebra co-Heyting algebra >.
type Coheyting a = (Lattice a, Algebra 'L a)

-- | A < https://ncatlab.org/nlab/show/co-Heyting+algebra bi-Heyting algebra >.
--
-- /Laws/:
--
-- > neg x <= non x
--
-- with equality occurring iff /a/ is a 'Boolean' algebra.
type Biheyting a = (Coheyting a, Heyting a)

-- | Heyting and co-Heyting algebras
--
-- A Heyting algebra is a bound, distributive lattice equipped with an
-- implication operation.
--
-- * The complete of closed subsets of a topological space is the primordial
-- example of a /Coheyting/ (co-Algebra) algebra.
--
-- * The dual complete of open subsets of a topological space is likewise
-- the primordial example of a /Heyting/ algebra.
--
-- /Coheyting/:
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
-- /Heyting/:
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
class Semilattice k a => Algebra k a where
    -- | The defining connection of a (co-)Heyting algebra.
    --
    -- > algebra @'L x = CastL (\\ x) (\/ x)
    -- > algebra @'R x = CastR (x /\) (x //)
    algebra :: a -> Cast k a a

-------------------------------------------------------------------------------
-- Heyting
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
-- > x <= y <=> x // y = top
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
(//) :: Algebra 'R a => a -> a -> a
(//) = floor . algebra

-- | Intuitionistic equivalence.
--
-- When @a@ is /Bool/ this is 'if-and-only-if'.
iff :: Algebra 'R a => a -> a -> a
iff x y = (x // y) /\ (y // x)

-- | Logical negation.
--
-- @ 'neg' x = x '//' 'bottom' @
--
-- /Laws/:
--
-- > neg bottom = top
-- > neg top = bottom
-- > x <= neg (neg x)
-- > neg (x \/ y) <= neg x
-- > neg (x // y) = neg (neg x) /\ neg y
-- > neg (x \/ y) = neg x /\ neg y
-- > x /\ neg x = bottom
-- > neg (neg (neg x)) = neg x
-- > neg (neg (x \/ neg x)) = top
--
-- Some logics may in addition obey < https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra De Morgan conditions >.
neg :: Heyting a => a -> a
neg x = x // bottom

-- | The Algebra (< https://ncatlab.org/nlab/show/excluded+middle not necessarily excluded>) middle operator.
middle :: Heyting a => a -> a
middle x = x \/ neg x

-- | Default constructor for a Algebra algebra.
heyting :: Meet a => (a -> a -> a) -> a -> Cast 'R a a
heyting f a = CastR (a /\) (a `f`)

-- | An adjunction between a Algebra algebra and its Boolean sub-algebra.
--
-- Double negation is a meet-preserving monad.
booleanR :: Heyting a => Cast 'R a a
booleanR = CastR (neg . neg) inj
  where
    -- Check that /x/ is a regular element
    -- See https://ncatlab.org/nlab/show/regular+element
    inj x = if x ~~ (neg . neg) x then x else bottom

-------------------------------------------------------------------------------
-- Coheyting
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
-- > x >= y <=> y \\ x = bottom
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
(\\) :: Algebra 'L a => a -> a -> a
(\\) = flip $ ceiling . algebra

-- | Intuitionistic co-equivalence.
equiv :: Algebra 'L a => a -> a -> a
equiv x y = (x \\ y) \/ (y \\ x)

-- | Logical < https://ncatlab.org/nlab/show/co-Heyting+negation co-negation >.
--
-- @ 'non' x = 'top' '\\' x @
--
-- /Laws/:
--
-- > non bottom = top
-- > non top = bottom
-- > x >= non (non x)
-- > non (x /\ y) >= non x
-- > non (y \\ x) = non (non x) \/ non y
-- > non (x /\ y) = non x \/ non y
-- > x \/ non x = top
-- > non (non (non x)) = non x
-- > non (non (x /\ non x)) = bottom
non :: Coheyting a => a -> a
non x = top \\ x

-- | The co-Heyting < https://ncatlab.org/nlab/show/co-Heyting+boundary boundary > operator.
--
-- > x = boundary x \/ (non . non) x
-- > boundary (x /\ y) = (boundary x /\ y) \/ (x /\ boundary y)  -- (Leibniz rule)
-- > boundary (x \/ y) \/ boundary (x /\ y) = boundary x \/ boundary y
boundary :: Coheyting a => a -> a
boundary x = x /\ non x

-- | Default constructor for a co-Heyting algebra.
coheyting :: Join a => (a -> a -> a) -> a -> Cast 'L a a
coheyting f a = CastL (`f` a) (\/ a)

-- | An adjunction between a co-Heyting algebra and its Boolean sub-algebra.
--
-- Double negation is a join-preserving comonad.
booleanL :: Coheyting a => Cast 'L a a
booleanL = CastL inj (non . non)
  where
    -- Check that /x/ is a regular element
    -- See https://ncatlab.org/nlab/show/regular+element
    inj x = if x ~~ (non . non) x then x else top

-------------------------------------------------------------------------------
-- Symmetric
-------------------------------------------------------------------------------

-- | Symmetric Heyting algebras
--
-- A symmetric Heyting algebra is a <https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra De Morgan >
-- bi-Algebra algebra with an idempotent, antitone negation operator.
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
    not :: a -> a

    infixl 4 `xor`

    -- | Exclusive or.
    --
    -- > xor x y = (x \/ y) /\ (not x \/ not y)
    xor :: a -> a -> a
    xor x y = (x \/ y) /\ not (x /\ y)

-- | Left converse operator.
converseL :: Symmetric a => a -> a
converseL x = top \\ not x

-- | Right converse operator.
converseR :: Symmetric a => a -> a
converseR x = not x // bottom

-- | Default constructor for a Heyting algebra.
symmetricR :: Symmetric a => a -> Cast 'R a a
symmetricR = heyting $ \x y -> not (not y \\ not x)

-- | Default constructor for a co-Heyting algebra.
symmetricL :: Symmetric a => a -> Cast 'L a a
symmetricL = coheyting $ \x y -> not (not y // not x)

-------------------------------------------------------------------------------
-- Boolean
-------------------------------------------------------------------------------

-- | Boolean algebras.
--
-- < https://ncatlab.org/nlab/show/Boolean+algebra Boolean algebras > are
-- symmetric Algebra algebras that satisfy both the law of excluded middle
-- and the law of law of non-contradiction:
--
-- > x \/ neg x = top
-- > x /\ non x = bottom
--
-- If /a/ is Boolean we also have:
--
-- > non = not = neg
class Symmetric a => Boolean a where
    -- | A witness to the lawfulness of a boolean algebra.
    boolean :: Cast k a a
    boolean = Cast (converseR . converseL) id (converseL . converseR)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semilattice k () where
    bound = bounded
    semilattice = ordered

instance Algebra 'L () where algebra = coheyting impliesL
instance Algebra 'R () where algebra = heyting impliesR
instance Symmetric () where not = id
instance Boolean ()

instance Semilattice k Bool where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Bool where algebra = coheyting impliesL
instance Algebra 'R Bool where algebra = heyting impliesR
instance Symmetric Bool where not = P.not
instance Boolean Bool

instance Semilattice k Ordering where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Ordering where algebra = coheyting impliesL
instance Algebra 'R Ordering where algebra = heyting impliesR
instance Symmetric Ordering where
    not LT = GT
    not EQ = EQ
    not GT = LT

instance Semilattice k Word8 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Word8 where algebra = coheyting impliesL
instance Algebra 'R Word8 where algebra = heyting impliesR

instance Semilattice k Word16 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Word16 where algebra = coheyting impliesL
instance Algebra 'R Word16 where algebra = heyting impliesR

instance Semilattice k Word32 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Word32 where algebra = coheyting impliesL
instance Algebra 'R Word32 where algebra = heyting impliesR

instance Semilattice k Word64 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Word64 where algebra = coheyting impliesL
instance Algebra 'R Word64 where algebra = heyting impliesR

instance Semilattice k Word where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Word where algebra = coheyting impliesL
instance Algebra 'R Word where algebra = heyting impliesR

instance Semilattice k Int8 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Int8 where algebra = coheyting impliesL
instance Algebra 'R Int8 where algebra = heyting impliesR

instance Semilattice k Int16 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Int16 where algebra = coheyting impliesL
instance Algebra 'R Int16 where algebra = heyting impliesR

instance Semilattice k Int32 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Int32 where algebra = coheyting impliesL
instance Algebra 'R Int32 where algebra = heyting impliesR

instance Semilattice k Int64 where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Int64 where algebra = coheyting impliesL
instance Algebra 'R Int64 where algebra = heyting impliesR

instance Semilattice k Int where
    bound = bounded
    semilattice = ordered

instance Algebra 'L Int where algebra = coheyting impliesL
instance Algebra 'R Int where algebra = heyting impliesR

{-
instance Semilattice k Float where
  bound = conn
  semilattice = conn

instance Semilattice k Double where
  bound = conn
  semilattice = conn

instance Semilattice k Rational where
  bound = conn
  semilattice = conn

instance Semilattice k Positive where
  bound = conn
  semilattice = conn
-}
-------------------------------------------------------------------------------
-- Instances: product types
-------------------------------------------------------------------------------

instance (Lattice a, Lattice b) => Semilattice k (a, b) where
    bound = Cast (const (bottom, bottom)) (const ()) (const (top, top))
    semilattice = Cast (uncurry joinTuple) fork (uncurry meetTuple)

instance (Heyting a, Heyting b) => Algebra 'R (a, b) where
    algebra (a, b) = algebra a `strong` algebra b

instance (Coheyting a, Coheyting b) => Algebra 'L (a, b) where
    algebra (a, b) = algebra a `strong` algebra b

instance (Symmetric a, Symmetric b) => Symmetric (a, b) where
    not = bimap not not

instance (Boolean a, Boolean b) => Boolean (a, b)

-------------------------------------------------------------------------------
-- Instances: sum types
-------------------------------------------------------------------------------

instance Join a => Semilattice 'L (Maybe a) where
    bound = CastL (const Nothing) (const ())
    semilattice = CastL (uncurry joinMaybe) fork

instance Meet a => Semilattice 'R (Maybe a) where
    bound = CastR (const ()) (const $ Just top)
    semilattice = CastR fork (uncurry meetMaybe)

instance Heyting a => Algebra 'R (Maybe a) where
    algebra = heyting f
      where
        f (Just a) (Just b) = Just (a // b)
        f Nothing _ = Just top
        f _ Nothing = Nothing

instance Join a => Semilattice 'L (Extended a) where
    bound = Cast (const NegInf) (const ()) (const PosInf)
    semilattice = CastL (uncurry joinExtended) fork

instance Meet a => Semilattice 'R (Extended a) where
    bound = Cast (const NegInf) (const ()) (const PosInf)
    semilattice = CastR fork (uncurry meetExtended)

instance Heyting a => Algebra 'R (Extended a) where
    algebra = heyting f
      where
        Finite a `f` Finite b
            | a <~ b = PosInf
            | otherwise = Finite (a // b)
        PosInf `f` a = a
        _ `f` PosInf = PosInf
        NegInf `f` _ = PosInf
        _ `f` NegInf = NegInf

-- | All minimal elements of the upper lattice cover all maximal elements of the lower lattice.
instance (Join a, Join b) => Semilattice 'L (Either a b) where
    bound = CastL (const $ Left bottom) (const ())
    semilattice = CastL (uncurry joinEither) fork

instance (Meet a, Meet b) => Semilattice 'R (Either a b) where
    bound = CastR (const ()) (const $ Right top)
    semilattice = CastR fork (uncurry meetEither)

-- |
-- Subdirectly irreducible Algebra algebra.
instance Heyting a => Algebra 'R (Either a ()) where
    algebra = heyting f
      where
        (Left a) `f` (Left b)
            | a <~ b = top
            | otherwise = Left (a // b)
        (Right _) `f` a = a
        _ `f` (Right _) = top

instance Heyting a => Algebra 'R (Either () a) where
    algebra = heyting f
      where
        f (Right a) (Right b) = Right (a // b)
        f (Left _) _ = Right top
        f _ (Left _) = bottom

-------------------------------------------------------------------------------
-- Instances: collections
-------------------------------------------------------------------------------

{-
instance Total a => Connection k (Set.Set a, Set.Set a) (Set.Set a) where
    semilattice = Cast (uncurry Set.union) fork (uncurry Set.intersection)

instance Connection 'L () IntSet.IntSet where
    bound = CastL (const IntSet.empty) (const ())

instance Connection k (IntSet.IntSet, IntSet.IntSet) IntSet.IntSet where
    semilattice = Cast (uncurry IntSet.union) fork (uncurry IntSet.intersection)

instance (Total a, Preorder b) => Connection 'L () (Map.Map a b) where
    bound = CastL (const Map.empty) (const ())

instance (Total a, Left (b, b) b) => Connection 'L (Map.Map a b, Map.Map a b) (Map.Map a b) where
    semilattice = CastL (uncurry $ Map.unionWith join) fork

instance (Total a, Right (b, b) b) => Connection 'R (Map.Map a b, Map.Map a b) (Map.Map a b) where
    semilattice = CastR fork (uncurry $ Map.intersectionWith meet)

instance Preorder a => Connection 'L () (IntMap.IntMap a) where
    bound = CastL (const IntMap.empty) (const ())

instance Left (a, a) a => Connection 'L (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    semilattice = CastL (uncurry $ IntMap.unionWith join) fork

instance Right (a, a) a => Connection 'R (IntMap.IntMap a, IntMap.IntMap a) (IntMap.IntMap a) where
    semilattice = CastR fork (uncurry $ IntMap.intersectionWith meet)
-}

instance Total a => Semilattice 'L (Set.Set a) where
    bound = CastL (const Set.empty) (const ())
    semilattice = CastL (uncurry Set.union) fork

instance Total a => Algebra 'L (Set.Set a) where
    algebra = coheyting (Set.\\)

--instance (Total a, U.Finite a) => Algebra 'R (Set.Set a) where
--  algebra = symmetricR

--instance (Total a, U.Finite a) => Symmetric (Set.Set a) where
--  not = non --(U.universe Set.\\)

--instance (Total a, U.Finite a) => Boolean (Set.Set a) where

instance Semilattice k IntSet.IntSet where
    bound = Cast (const IntSet.empty) (const ()) (const $ IntSet.fromList [minBound .. maxBound])
    semilattice = Cast (uncurry IntSet.union) fork (uncurry IntSet.intersection)

instance Algebra 'L IntSet.IntSet where
    algebra = coheyting (IntSet.\\)

instance Algebra 'R IntSet.IntSet where
    --heyting = heyting $ \x y -> non x \/ y
    algebra = symmetricR

instance Symmetric IntSet.IntSet where
    not = non --(U.universe IntSet.\\)

{-
instance Algebra 'R IntSet.IntSet where
  --heyting = heyting $ \x y -> non x \/ y
  algebra = symmetricR

instance Symmetric IntSet.IntSet where
  not = non --(U.universe IntSet.\\)

instance Boolean IntSet.IntSet where

-}

instance (Total k, Join a) => Semilattice 'L (Map.Map k a) where
    bound = CastL (const Map.empty) (const ())

    semilattice = CastL f fork
      where
        f = uncurry $ Map.unionWith (\/)

instance (Total k, Join a) => Algebra 'L (Map.Map k a) where
    algebra = coheyting (Map.\\)

instance (Join a) => Semilattice 'L (IntMap.IntMap a) where
    bound = CastL (const IntMap.empty) (const ())

    semilattice = CastL f fork
      where
        f = uncurry $ IntMap.unionWith (\/)

instance (Join a) => Algebra 'L (IntMap.IntMap a) where
    algebra = coheyting (IntMap.\\)

-- Internal

-------------------------
fork :: a -> (a, a)
fork x = (x, x)

impliesL :: (Total a, P.Bounded a) => a -> a -> a
impliesL x y = if y < x then x else P.minBound

impliesR :: (Total a, P.Bounded a) => a -> a -> a
impliesR x y = if x > y then y else P.maxBound

joinTuple :: (Semilattice 'L a, Semilattice 'L b) => (a, b) -> (a, b) -> (a, b)
joinTuple (x1, y1) (x2, y2) = (x1 \/ x2, y1 \/ y2)

meetTuple :: (Semilattice 'R a, Semilattice 'R b) => (a, b) -> (a, b) -> (a, b)
meetTuple (x1, y1) (x2, y2) = (x1 /\ x2, y1 /\ y2)

joinMaybe :: Join a => Maybe a -> Maybe a -> Maybe a
joinMaybe (Just x) (Just y) = Just (x \/ y)
joinMaybe u@(Just _) _ = u
joinMaybe _ u@(Just _) = u
joinMaybe Nothing Nothing = Nothing

meetMaybe :: Meet a => Maybe a -> Maybe a -> Maybe a
meetMaybe Nothing Nothing = Nothing
meetMaybe Nothing _ = Nothing
meetMaybe _ Nothing = Nothing
meetMaybe (Just x) (Just y) = Just (x /\ y)

joinExtended :: Join a => Extended a -> Extended a -> Extended a
joinExtended PosInf _ = PosInf
joinExtended _ PosInf = PosInf
joinExtended (Finite x) (Finite y) = Finite (x \/ y)
joinExtended NegInf y = y
joinExtended x NegInf = x

meetExtended :: Meet a => Extended a -> Extended a -> Extended a
meetExtended PosInf y = y
meetExtended x PosInf = x
meetExtended (Finite x) (Finite y) = Finite (x /\ y)
meetExtended NegInf _ = NegInf
meetExtended _ NegInf = NegInf

joinEither :: (Join a, Join b) => Either a b -> Either a b -> Either a b
joinEither (Right x) (Right y) = Right (x \/ y)
joinEither u@(Right _) _ = u
joinEither _ u@(Right _) = u
joinEither (Left x) (Left y) = Left (x \/ y)

meetEither :: (Meet a, Meet b) => Either a b -> Either a b -> Either a b
meetEither (Left x) (Left y) = Left (x /\ y)
meetEither l@(Left _) _ = l
meetEither _ l@(Left _) = l
meetEither (Right x) (Right y) = Right (x /\ y)
