{-# LANGUAGE CPP                        #-}
{-# LANGUAGE Safe                       #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Semilattice (
    bottom
  , top
  , (∧)
  , (∨)
  , Join(..)
  , Meet(..)
  , module Data.Semilattice 
) where

import safe Control.Applicative
import safe Data.Bool
import safe Data.Complex
import safe Data.Connection
import safe Data.Maybe
import safe Data.Either
import safe Data.Fixed
import safe Data.Float
import safe Data.Foldable hiding (join, meet)
import safe Data.Group
import safe Data.Int
import safe Data.List (unfoldr)
import safe Data.List.NonEmpty hiding (filter, unfoldr)
import safe Data.Magma
import safe Data.Prd
import safe Data.Ord
import safe Data.Semiring
import safe Data.Dioid
import safe Data.Semigroup
import safe Data.Semigroup
import safe Data.Semigroup.Join
import safe Data.Semigroup.Foldable
import safe Data.Semigroup.Meet
import safe Data.Tuple
import safe Data.Word
import safe Foreign.C.Types (CFloat(..),CDouble(..))
import safe GHC.Generics (Generic)
import safe GHC.Real hiding (Fractional(..), div, (^^), (^), (%))
import safe Numeric.Natural
import safe Data.Ratio

import safe Prelude ( Eq(..), Ord(..), Show, Ordering(..), Applicative(..), Functor(..), Monoid(..), Semigroup(..), id, (.), ($), flip, (<$>), Integer, Float, Double)
import safe qualified Prelude as P

import qualified Control.Category as C 
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet


{-

A partially ordered set is a directed-complete partial order (dcpo) if each of its directed subsets has a supremum. A subset of a partial order is directed if it is non-empty and every pair of elements has an upper bound in the subset. In the literature, dcpos sometimes also appear under the label up-complete poset.



-}

--(a ∧ b) ⊗ c = (a ⊗ c) ∧ (b ⊗ c), c ⊗ (a ∧ b) = (c ⊗ a) ∧ (c ⊗ b)
-- (meet x y) ∧ z = x ∧ z `meet` y ∧ z

-- idempotent sup dioids ? complete (join-semi)lattices derived from <~?
--connr-distributivity (the group (E\{ε}, ⊗) is therefore reticulated)
--
-- mon zero = const Nothing

-- bounded meet semilattice
-- need the codistributive property & absorbtion & commutativity

{-
If E is a distributive lattice, then (E, ∨, ∧) is a doublyidempotent dioid, the order relation (canonical) of the dioid being defined as:
a ≤ b ⇔ a ∨ b = b.
Conversely, let (E, ⊕, ⊗) be a doubly-idempotent dioid for which ≤, the canonical
order relation relative to the law ⊕ is also a canonical order relation for ⊗:
x ≤ y ⇔ x ⊗ y = x.
Then E is a distributive lattice.
-}


{-
< https://en.wikipedia.org/wiki/Graded_poset >
class Prd a => Graded a where
  rank :: a -> Natural

instance Graded Set, IntSet, Natural
-}

-- Lattice types






type BoundedJoinSemilattice a = (Prd a, (Join-Monoid) a)



type BoundedMeetSemilattice a = (Prd a, (Meet-Monoid) a)

type LatticeLaw a = (JoinSemilattice a, MeetSemilattice a)

type BoundedLatticeLaw a = (BoundedJoinSemilattice a, BoundedMeetSemilattice a)

type LowerBoundedLattice a = (Lattice a, (Join-Monoid) a)

type UpperBoundedLattice a = (Lattice a, (Meet-Monoid) a)

type BoundedLattice a = (Lattice a, BoundedLatticeLaw a)

type Distributive a = (Presemiring a, Lattice a)

{-
class (Lattice a, BoundedLatticeLaw a) => BoundedLattice a


instance BoundedLattice ()
instance BoundedLattice Bool
instance (Prd a, UpperBounded a) => BoundedLattice (Maybe a)
--instance (Prd a, UpperBounded a) => BoundedLattice (IntMap.IntMap a)
--instance (Ord k, (Meet-Monoid) k, Prd a, UpperBounded a) => BoundedLattice (Map.Map k a)
-}

--type Bounded



--type MinimalLatticeLaw a = (Prd a, (Join-BoundedSemilattice) a, (Meet-Semilattice) a)

--type MaximalLatticeLaw a = (Prd a, (Join-Semilattice) a, (Meet-BoundedSemilattice) a)

-- | Lattices.
--
-- A lattice is a partially ordered set in which every two elements have a unique join 
-- (least upper bound or supremum) and a unique meet (greatest lower bound or infimum). 
--
-- /Neutrality/
--
-- @
-- x '∨' 'minimal' '==' x
-- x '∧' 'maximal' '==' x
-- @
--
-- /Associativity/
--
-- @
-- x '∨' (y '∨' z) '==' (x '∨' y) '∨' z
-- x '∧' (y '∧' z) '==' (x '∧' y) '∧' z
-- @
--
-- /Commutativity/
--
-- @
-- x '∨' y '==' y '∨' x
-- x '∧' y '==' y '∧' x
-- @
--
-- /Idempotency/
--
-- @
-- x '∨' x '==' x
-- x '∧' x '==' x
-- @
--
-- /Absorption/
--
-- @
-- (x '∨' y) '∧' y '==' y
-- (x '∧' y) '∨' y '==' y
-- @
--
-- See <http://en.wikipedia.org/wiki/Lattice_(order)> and <http://en.wikipedia.org/wiki/Absorption_law>.
--
-- Note that distributivity is _not_ a requirement for a lattice,
-- however distributive lattices are idempotent, commutative dioids.
-- 
class LatticeLaw a => Lattice a




-- | Birkhoff's self-dual < https://en.wikipedia.org/wiki/Median_algebra ternary median > operation.
--
-- If the lattice is distributive then 'glb' has the following properties.
--
-- @ 
-- 'glb' x y y '==' y
-- 'glb' x y z '==' 'glb' z x y
-- 'glb' x y z '==' 'glb' x z y
-- 'glb' ('glb' x w y) w z '==' 'glb' x w ('glb' y w z)
-- @
--
-- >>> glb 1 2 3 :: Int
-- 2
-- >>> glb (fromList [1..3]) (fromList [3..5]) (fromList [5..7]) :: Set Int
-- fromList [3,5]
--
-- See 'Data.Dioid.Property'.
-- 
glb :: Lattice a => a -> a -> a -> a
glb x y z = (x ∨ y) ∧ (y ∨ z) ∧ (z ∨ x)

lub :: Lattice a => a -> a -> a -> a
lub x y z = (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x)

-- @ 'join' :: 'Lattice' a => 'Minimal' a => 'Set' a -> a @
--
join :: (Join-Monoid) a => Lattice a => Foldable f => f a -> a
join = joinWith id

-- >>> joinWith MaxMin $ [IntSet.fromList [1..5], IntSet.fromList [2..4]]
-- MaxMin {unMaxMin = fromList [2,3,4]}
joinWith :: (Join-Monoid) a => Foldable t => (b -> a) -> t b -> a
joinWith f = foldr' ((∨) . f) bottom
{-# INLINE joinWith #-}

meet :: (Meet-Monoid) a => Lattice a => Foldable f => f a -> a
meet = meetWith id

-- | Fold over a collection using the multiplicative operation of an arbitrary semiring.
-- 
-- @
-- 'meet' f '==' 'Data.foldr'' ((*) . f) 'top'
-- @
--
--
-- >>> meetWith Just [1..5 :: Int]
-- Just 120
--
meetWith :: (Meet-Monoid) a => Foldable t => (b -> a) -> t b -> a
meetWith f = foldr' ((∧) . f) top
{-# INLINE meetWith #-}

-- | The join of a list of join-semilattice elements (of length at least top)
join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id

-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--

--(1 :| [2..5 :: Int]) ∧ (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> joinWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> joinWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
joinWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
joinWith1 f = unJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

-- | The meet of a list of meet-semilattice elements (of length at least top)
meet1 :: Lattice a => Foldable1 f => f a -> a
meet1 = meetWith1 id

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> meetWith1 Just $ 1 :| [2..5 :: Int]
-- Just 120
-- >>> meetWith1 First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
-- >>> meetWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
meetWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
meetWith1 f = unMeet . foldMap1 (Meet . f)
{-# INLINE meetWith1 #-}

{-
-- | Lattice morphism.
fromSubset :: Minimal a => Set a -> a
fromSubset = join

-- >>> join [1..5 :: Int]
-- 15
join :: (Join-Monoid) a => Lattice a => Foldable f => f a -> a
join = joinWith id

join1 :: Lattice a => Foldable1 f => f a -> a
join1 = joinWith1 id


-- >>> evalWith1 MaxMin $ (1 :| [2..5 :: Int]) :| [1 :| [2..5 :: Int]]
-- | Fold over a non-empty collection using the additive operation of an arbitrary semiring.
--
-- >>> joinWith1 First $ (1 :| [2..5 :: Int]) * (1 :| [2..5 :: Int])
-- First {getFirst = 1}
-- >>> joinWith1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
-- >>> joinWith1 Just $ 1 :| [2..5 :: Int]
-- Just 15
--
joinWith1 :: Foldable1 t => Lattice a => (b -> a) -> t b -> a
joinWith1 f = unJoin . foldMap1 (Join . f)
{-# INLINE joinWith1 #-}

-- >>> meet [1..5 :: Int]
-- 120
meet :: (Meet-Monoid) a => Lattice a => Foldable f => f a -> a
meet = meetWith id

--
-- | The meet of at a list of semiring elements (of length at least top)
meet1 :: Lattice a => Foldable1 f => f a -> a
meet1 = meetWith1 id



-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 :: Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 :: Int] []
-- 0
--
cross :: Foldable f => Applicative f => Lattice a => (Join-Monoid) a => f a -> f a -> a
cross a b = join $ liftA2 (*) a b
{-# INLINE cross #-}

-- | Cross-multiply two non-empty collections.
--
-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
--
cross1 :: Foldable1 f => Apply f => Lattice a => f a -> f a -> a
cross1 a b = join1 $ liftF2 (*) a b
{-# INLINE cross1 #-}

-- | Evaluate a semiring expression.
-- 
-- @ (a11 * .. * a1m) + (a21 * .. * a2n) + ... @
--
-- >>> eval [[1, 2], [3, 4 :: Int]] -- 1 * 2 + 3 * 4
-- 14
-- >>> eval $ sequence [[1, 2], [3, 4 :: Int]] -- 1 + 2 * 3 + 4
-- 21
--
eval :: Semiring a => Functor f => Foldable f => Foldable g => f (g a) -> a
eval = join . fmap meet

-- >>> evalWith Max [[1..4 :: Int], [0..2 :: Int]]
-- Max {getMax = 24}
evalWith :: Semiring r => Functor f => Functor g => Foldable f => Foldable g => (a -> r) -> f (g a) -> r
evalWith f = join . fmap meet . (fmap . fmap) f

eval1 :: Lattice a => Functor f => Foldable1 f => Foldable1 g => f (g a) -> a
eval1 = join1 . fmap meet1

-- >>>  evalWith1 (Max . Down) $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = Down 9}
-- >>>  evalWith1 Max $ (1 :| [2..5 :: Int]) :| [-5 :| [2..5 :: Int]]
-- Max {getMax = 15}
-- 
evalWith1 :: Lattice r => Functor f => Functor g => Foldable1 f => Foldable1 g => (a -> r) -> f (g a) -> r
evalWith1 f = join1 . fmap meet1 . (fmap . fmap) f

-}




{-

-- p. 337 e.g. (N, lcm, (*))
-- 1 is not absorbing for (*) (indeed, for a∈E,a=1,a×1=a /=1). (N, lcm,×) is therefore neither a semiring nor a dioid.


--Data.Semiring.Euclidean
newtype GCD a = GCD a
newtype LCM a = LCM a

instance Semigroup (Join (GCD Natural)) where (<>) = liftA2 gcd

instance Monoid (Join (GCD (PInf Natural))) where mempty = pure Inf

instance Semigroup (Meet (LCM Natural)) where (<>) = liftA2 lcm

instance Monoid (Meet (LCM Natural)) where mempty = pure 1 -- what about zero?


-}

-- Lattices
instance Lattice ()
instance Lattice Bool
instance Lattice Word
instance Lattice Word8
instance Lattice Word16
instance Lattice Word32
instance Lattice Word64
instance Lattice Natural
instance Lattice (Ratio Natural)

instance Lattice Int
instance Lattice Int8
instance Lattice Int16
instance Lattice Int32
instance Lattice Int64
instance Lattice Integer
instance Lattice Rational

instance Lattice Uni
instance Lattice Deci
instance Lattice Centi
instance Lattice Milli
instance Lattice Micro
instance Lattice Nano
instance Lattice Pico

instance Lattice a => Lattice (Down a)
instance (Prd a, Prd b, Lattice a, Lattice b) => Lattice (Either a b)
instance (Prd a, Lattice a) => Lattice (Maybe a)
instance (Prd a, Lattice a) => Lattice (IntMap.IntMap a)
instance Lattice IntSet.IntSet
instance Ord a => Lattice (Set.Set a)
instance (Ord k, Prd a, Lattice a) => Lattice (Map.Map k a)

newtype MaxMin a = MaxMin { unMaxMin :: a } deriving (Eq, Generic, Ord, Show, Functor)

instance Applicative MaxMin where
  pure = MaxMin
  MaxMin f <*> MaxMin a = MaxMin (f a)

instance Prd a => Prd (MaxMin a) where
  MaxMin a <~ MaxMin b = a <~ b

instance Ord a => Semigroup (Join (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ max

instance (Ord a, Minimal a) => Monoid (Join (MaxMin a)) where
  mempty = pure . pure $ minimal


instance Ord a => Semigroup (Meet (MaxMin a)) where
  (<>) = liftA2 . liftA2 $ min

instance (Ord a, Maximal a) => Monoid (Meet (MaxMin a)) where
  mempty = pure . pure $ maximal


instance (Ord a, Bound a) => Lattice (MaxMin a)






type family Idx a :: *

type instance Idx (Down a) = Down (Idx a)
type instance Idx Bool = Bool
type instance Idx Int8 = Int8
type instance Idx Int16 = Int16
type instance Idx Int32 = Int32
type instance Idx Int64 = Int64
type instance Idx Integer = Integer

type instance Idx Word8 = Word8
type instance Idx Word16 = Word16
type instance Idx Word32 = Word32
type instance Idx Word64 = Word64
type instance Idx Natural = Natural

type instance Idx Float = Ulp32


{-
https://en.wikipedia.org/wiki/Total_order#Chains
https://en.wikipedia.org/wiki/Completeness_(order_theory)
https://en.wikipedia.org/wiki/Chain-complete_partial_order
https://en.wikipedia.org/wiki/Linear_extension
-}

type Yoneda a = (Ideal a, Filter a)

-- Linear extension to an /a/-compatible poset?
--
-- See < >.
-- 
type Up a = (Ideal a, Semiring (Idx a))
type Dn a = (Filter a, Ring (Idx a))

type Index a = (Up a, Dn a)

-- | Yoneda representation for lattice ideals.
--
-- A subset /I/ of a lattice is an ideal if and only if it is a lower set 
-- that is closed under finite joins, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x ∨ y/ is also in /I/.
--
-- /Idx a/ is downward-closed:
--
-- * @'lower' x s && x '>~' y ==> 'lower' y s@
--
-- * @'lower' x s && 'lower' y s ==> 'connl' 'ideal' x '∨' 'connl' 'ideal' y '~<' s@
--
-- Finally /filter >>> ideal/ and /ideal >>> filter/ are both connections
-- on /a/ and /Idx a/ respectively.
--
-- See <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
--
class (Prd a, JoinSemilattice (Idx a)) => Ideal a where

  -- | Principal ideal generated by an element of /a/.
  ideal :: Conn (Idx a) a

  -- | Lower set in /a/ generated by an element in /Idx a/.
  lower :: Idx a -> a -> Bool
  lower i a = connr ideal a <~ i

-- | Yoneda representation for lattice filters.
--
-- A subset /I/ of a lattice is an filter if and only if it is an upper set 
-- that is closed under finite meets, i.e., it is nonempty and for all 
-- /x/, /y/ in /I/, the element /x ∧ y/ is also in /I/.
--
-- /upper/ and /lower/ commute with /Down/:
--
-- * @lower x y == upper (Down x) (Down y)@
--
-- * @lower (Down x) (Down y) == upper x y@
--
-- /Idx a/ is upward-closed:
--
-- * @'upper' x s && x '<~' y ==> 'upper' y s@
--
-- * @'upper' x s && 'upper' y s ==> 'connl' 'filter' x '∧' 'connl' 'filter' y '>~' s@
--
-- See <https://en.wikipedia.org/wiki/Filter_(mathematics)>
--
class (Prd a, MeetSemilattice (Idx a)) => Filter a where

  -- | Principal filter generated by an element of /a/.
  filter :: Conn a (Idx a)

  -- | Upper set in /a/ generated by an element in /Idx a/.
  upper :: Idx a -> a -> Bool
  upper i a = connl filter a >~ i




yoneda :: Yoneda a => Conn a a
yoneda = filter C.>>> ideal



--inc is (strictly?) monotone, dec is (strictly?) antitone, 
contains :: Prd a => a -> a -> a -> Bool
contains x y z = x <~ z && z <~ y



fromIndex :: Ideal a => Idx a -> a
fromIndex = connl ideal

toIndex :: Ideal a => a -> Idx a
toIndex = connr ideal

incBy :: Up a => Idx a -> a -> a
incBy x = fromIndex . (+x) . toIndex 

-- @ 'inc' '.' 'dec' = 'id' @
-- @ 'dec' '.' 'inc' = 'id' @
inc :: Up a => a -> a
inc = incBy one

-- | Covering relation on a partial order.
--
-- @ x '<.' y @ if and only if @ x `lt` y @ and there is no element /z/
-- such that @ x `lt` z '&&' z `lt` y @. 
--
-- See < https://en.wikipedia.org/wiki/Covering_relation >.
--
class Prd a => Covered a where
    (<.) :: a -> a -> Bool
    default (<.) :: Up a => a -> a -> Bool
    (<.) = covers

-- | A grading function on a partial order.
--
-- * @ 'lt' x y '==>' 'rank' x <~ 'rank' y @
-- * @ x '<.' y '==>' 'rank' x == 'rank' y '+' 1@
--
-- See < https://en.wikipedia.org/wiki/Graded_poset >.
class Covered a => Graded a where
    rank :: a -> Natural

-- interval :: Graded a => a -> a -> [a]

-- | Covering relation on /a/.
--
-- < https://en.wikipedia.org/wiki/Covering_relation >
--
covers :: Up a => a -> a -> Bool
covers x y = x `lt` y && all (not . lt x) (indexFrom x y)

-- | Constrained version of 'arr' from 'Control.Arrow'.
--
-- Essentially the same properties hold:
--
--  * @'arrow' id = 'Control.Category.id'@
--
--  * @'arrow' (f . g) = 'arrow' f >>> 'arrow' g@
--
--
--  * @'_1' ab >>> 'arrow' 'fst' = 'arrow' 'fst' >>> ab@
--
--  * @'_1' ('_1' ab) >>> 'arrow' 'assoc' = 'arrow' 'assoc' >>> '_1' ab@
--
--
--  * @ab >>> 'arrow' 'Left' = 'arrow' 'Left' >>> '_L' ab@
--
--  * @'_L' ('_L' ab) >>> 'arrow' 'assocsum' = 'arrow' 'assocsum' >>> '_L' ab@
--
-- where
--
-- > assoc ((a,b),c) = (a,(b,c))
-- > assocsum (Left (Left x)) = Left x
-- > assocsum (Left (Right y)) = Right (Left y)
-- > assocsum (Right z) = Right (Right z)
--
--
-- >>> conn = arrow (+1) :: Conn Int8 Int8
-- >>> connr conn minimal
-- -128
-- >>> connr conn 1
-- 0
--
-- >>> conn = arrow (+minSubf) :: Conn Float Float
-- >>> connr conn minimal
-- -Infinity
-- >>> connr conn (inc minimal)
-- -3.4028235e38
-- 
arrow :: (Up a, Minimal a, Prd b) => (a -> b) -> Conn a b
arrow f = Conn f (ascend' minimal f)




--TODO check closure

-- | 
--
-- @'ascend' y@ is the greatest element /x/ in the ascending
-- chain such that @g x '<~' y@.
--
ascend :: (Up a, Prd b) => a -> (a -> b) -> b -> a
ascend z g y = while (\x -> g x <~ y) le inc z

-- | 
--
-- @'ascend'' y@ is the greatest element /x/ in the ascending
-- chain such that @not $ g z '>~' y@.
--
ascend' :: (Up a, Prd b) => a -> (a -> b) -> b -> a
ascend' z g y = until (\x -> g x >~ y) le inc z

-- | 
--
-- @'descend' x@ is the least element /y/ in the descending
-- chain such that @f y '>~' x@.
--
descend :: (Dn a, Prd b) => a -> (a -> b) -> b -> a
descend z f x = while (\y -> f y >~ x) ge dec z
-- left


incdec :: Index a => Conn a (Down a)
incdec = Conn f g where
  f = Down . inc
  g x = dec x' where Down x' = x

decBy :: Dn a => Idx a -> a -> a
decBy x = connr filter . (+ (negate x)) . connl filter 

dec :: Dn a => a -> a
dec = decBy one

coarrow :: (Dn a, Maximal a, Prd b) => (a -> b) -> Conn b a
coarrow g = Conn (descend' maximal g) g

-- | 
--
-- @'descend'' x@ is the least element /y/ in the descending
-- chain such that @not $ f y '<~' x@.
--
descend' :: (Dn a, Prd b) => a -> (a -> b) -> b -> a
descend' z f x = until (\y -> f y <~ x) ge dec z

--mapWithIdx :: (Idx a -> a -> a) -> a -> a -> a

foldWithIdx :: (Eq a, Up a) => (Idx a -> a -> a) -> a -> a -> a
foldWithIdx f x y = foldr' f x $ toIndex <$> indexFromTo x y 

{-
indexTo' :: (Eq a, Index a) => Interval a -> [a]
indexTo' = maybe [] (\(x,y) -> indexFrom (inc x) y) . endpts

enumerate :: Index a => a -> a -> [a]
enumerate x y = flip evalState x $
  whileM (get >>= \z -> return (z <~ y)) (modify inc >> get) 
-}
-- | Generate a half-open interval /[x, y)/.
--
-- >>> indexFrom @Float 1 (inc 1)
-- [1.0]
--
indexFrom :: Up a => a -> a -> [a]
indexFrom x y = x : unfoldr f x where
  f x = let x' = inc x in if x' `gt` x && x' `lt` y
                             then Just (x, x') 
                             else Nothing

-- | Generate a half-open interval /(x, y]/.
--
-- >>> indexTo @Float 1 (inc 1)
-- [1.0000001]
--
indexTo :: (Eq a, Up a) => a -> a -> [a]
indexTo x y = indexFromTo (inc x) y

-- | Generate a closed interval /[x, y]/.
--
-- Returns the list of values in the interval defined by a bounding pair.
--
-- Lawful variant of 'enumFromTo'.
--
-- >>> indexFromTo @Float 1 (inc 1)
-- [1.0,1.0000001]
--
indexFromTo :: (Eq a, Up a) => a -> a -> [a]
indexFromTo x y = unfoldr f x where
  f x = let x' = inc x in if x' `gt` x && x <~ y
                             then Just (x, x') 
                             else Nothing


-- | Lawful variant of 'enumFromThenTo'.
indexFromToBy :: (Eq a, Up a) => Idx a -> a -> a -> [a]
indexFromToBy i x y = unfoldr f x where
  f x = let x' = incBy i x in if x' `gt` x && x' <~ y
                             then Just (x, x') 
                             else Nothing

instance Filter a => Ideal (Down a) where
  ideal = dual filter
  lower (Down r) (Down a) = upper @a r a

instance Ideal a => Filter (Down a) where
  filter = dual ideal
  upper (Down r) (Down a) = lower @a r a

#define deriveIdeal(ty)       \
instance Ideal ty where {     \
   ideal = C.id               \
;  {-# INLINE ideal #-}       \
;  lower = (>~)               \
;  {-# INLINE lower #-}       \
}

#define deriveFilter(ty)       \
instance Filter ty where {     \
   filter = C.id               \
;  {-# INLINE filter #-}       \
;  upper = (<~)               \
;  {-# INLINE upper #-}       \
}



deriveIdeal(Bool)
deriveIdeal(Int8)
deriveIdeal(Int16)
deriveIdeal(Int32)
deriveIdeal(Int64)
deriveIdeal(Integer)
deriveIdeal(Word8)
deriveIdeal(Word16)
deriveIdeal(Word32)
deriveIdeal(Word64)
deriveIdeal(Natural)

--deriveIdeal(Int)
--deriveIdeal(Word)

instance Ideal Float where
  ideal = u32f32



deriveFilter(Bool)
deriveFilter(Int8)
deriveFilter(Int16)
deriveFilter(Int32)
deriveFilter(Int64)
deriveFilter(Integer)
deriveFilter(Word8)
deriveFilter(Word16)
deriveFilter(Word32)
deriveFilter(Word64)
deriveFilter(Natural)





