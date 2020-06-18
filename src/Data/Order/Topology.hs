{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language DataKinds           #-}
{-# Language KindSignatures      #-}
{-# Language Safe                #-}

module Data.Order.Topology (
  -- * Left and right Alexandrov topologies
    Topology
  , Open()
  , (?)
  , base
  , bound
  , member
  , valid
  -- ** The left (/Inf/) topology
  , Inf
  , inf
  , upper
  , upper'
  , lfilter
  -- ** The right (/Sup/) topology
  , Sup 
  , sup
  , lower
  , lower'
  , rfilter
) where

import safe Control.Category (id,(.))
import safe Control.Applicative (liftA2)
import safe Data.Connection.Type
import safe Data.Foldable (foldl')
import safe Data.Semigroup.Join
import safe Data.Lattice
import safe Data.Lattice.Heyting
import safe Data.Order
import safe Data.Order.Interval
import safe Data.Universe.Class (Finite(..))
import safe Prelude hiding (id, (.), Bounded, Eq(..), Ord(..))
import safe qualified Data.Eq as Eq

import Data.Int

-- | A separated left or right < https://en.wikipedia.org/wiki/Alexandrov_topology Alexandrov topology >.
data Topology = Inf | Sup

-- | A pointed open set in a separated Alexandrov topology.
--
data Open (t :: Topology) a = Open (a -> Bool) a a

infix 4 ?

(?) :: Open t a -> a -> Bool
(?) = flip member

base :: Open t a -> a
base (Open _ x _) = x

bound :: Open t a -> a
bound (Open _ _ y) = y

valid :: Open t a -> Bool
valid (Open f x _) = f x

member :: a -> Open t a -> Bool
member a (Open f _ _) = f a

-- Up-set ideals
up :: Preorder a => a -> a -> Bool
up a = (a <~)

-- Up-set anti-ideals
up' :: Preorder a => a -> a -> Bool
up' a = fmap not (a <~)

-- Down-set ideals
down :: Preorder a => a -> a -> Bool
down a = (<~ a)

-- Down-set anti-ideals
down' :: Preorder a => a -> a -> Bool
down' a = fmap not (<~ a)

---------------------------------------------------------------------
-- Inf
---------------------------------------------------------------------

type Inf = Open 'Inf

-- | Create an upper set.
--
-- > inf = upper id
inf :: UpperBounded a => a -> Inf a
inf = upper id

-- | Create an upper set with a connection.
--
-- > upper c = upper' c . singleton
upper :: UpperBounded a => Conn a b -> a -> Inf b
upper (Conn f g) x = Open (up x . g) (f x) (f top)

-- | Map an interval to an open set in the /Inf/ topology with a connection.
--
-- >>> upper' (tripl f64f32) $ 0 ... 2*pi
-- 0.0 ... 6.2831855
--
upper' :: (UpperBounded a, Lattice b) => Conn a b -> Interval a -> Inf b
upper' c@(Conn f g) i = lfilter (f h) $ upper c l where (l,h) = maybe (top, top) id $ endpts i

infixr 5 `lfilter`

-- | Filter an open set with an anti-filter.
--
-- Intersecting with an incomparable element cuts out everything
-- larger than its join with the base point:
--
-- >>> p = inf pi :: Inf Double
-- >>> p ? 1/0
-- True
-- >>> lfilter (0/0) p ? 1/0
-- False
--
-- An example w/ the set inclusion lattice:
-- >>> x = Set.fromList [6,40] :: Set.Set Word8
-- >>> y = Set.fromList [1,6,9] :: Set.Set Word8
-- >>> z = lfilter y $ inf x
-- fromList [6,40] ... fromList [1,6,9,40]
-- >>> z ? Set.fromList [1,6,40]
-- True
-- >>> z ? Set.fromList [6,9,40]
-- True
-- >>> z ? Set.fromList [1,6,9,40]
-- False
--
lfilter :: Lattice a => a -> Inf a -> Inf a
lfilter a p@(Open f l r) = if down' l a then Open (f /\ up' a) l (glb l a r) else p

---------------------------------------------------------------------
-- Sup
---------------------------------------------------------------------

type Sup = Open 'Sup

-- | Create a lower set.
--
sup :: LowerBounded a => a -> Sup a
sup = lower id

-- | Create a lower set with a connection.
--
-- > lower c = lower' c . singleton
--
-- >>> valid . pull (tripr f64f32) $ lower pi
-- True
-- 
lower :: LowerBounded b => Conn a b -> b -> Sup a
lower (Conn f g) x = Open (down x . f) (g x) (g bottom)

-- | Map an interval to an open set in the /Sup/ topology with a connection.
--
-- >>> lower' (tripr f64f32) $ 0 ... 2*pi
-- 0.0 ... 6.283185
--
lower' :: (LowerBounded b, Lattice a) => Conn a b -> Interval b -> Sup a
lower' c@(Conn f g) i = rfilter (g l) $ lower c h where (l,h) = maybe (bottom, bottom) id $ endpts i

infixl 5 `rfilter`

-- | Filter an open set with an anti-ideal.
-- 
-- >>> p = sup pi :: Sup Double
-- >>> p ? -1/0
-- True
-- >>> rfilter (0/0) p ? -1/0
-- False
--
rfilter :: Lattice a => a -> Sup a -> Sup a
rfilter a p@(Open f r l) = if up' r a then Open (f /\ down' a) r (lub l a r) else p

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------


--deriving instance Eq a => Eq (Open t a)
instance Show a => Show (Inf a) where
  show (Open _ l r) = show l ++ " ... " ++ show r

instance Show a => Show (Sup a) where
  show (Open _ l r) = show r ++ " ... " ++ show l

-- |
-- Note that '~~' is strictly weaker than '==', as it ignores the 
-- location of the base point.
instance Finite a => Preorder (Open t a) where
  (Open f _ _) <~ (Open g _ _) = f <~ g

instance Lattice a => Semigroup (Join (Inf a)) where
  (<>) = liftA2 joinInf

instance UpperBounded a => Monoid (Join (Inf a)) where
  mempty = pure $ inf top

instance Lattice a => Semigroup (Meet (Inf a)) where
  (<>) = liftA2 meetInf

instance Bounded a => Monoid (Meet (Inf a)) where
  mempty = pure $ inf bottom


joinInf :: Lattice a => Inf a -> Inf a -> Inf a
joinInf (Open f1 l1 r1) (Open f2 l2 r2) = Open (f1 \/ f2) (l1 /\ l2) (r1 \/ r2)

meetInf :: Lattice a => Inf a -> Inf a -> Inf a
meetInf (Open f1 l1 r1) (Open f2 l2 r2) = Open (f1 /\ f2) (l1 \/ l2) (r1 /\ r2)

instance (Finite a, Lattice a) => Lattice (Inf a)
instance (Finite a, Bounded a) => Bounded (Inf a)


instance Lattice a => Semigroup (Join (Sup a)) where
  (<>) = liftA2 joinSup

instance LowerBounded a => Monoid (Join (Sup a)) where
  mempty = pure $ sup bottom

instance Lattice a => Semigroup (Meet (Sup a)) where
  (<>) = liftA2 meetSup

instance Bounded a => Monoid (Meet (Sup a)) where
  mempty = pure $ sup top

joinSup :: Lattice a => Sup a -> Sup a -> Sup a
joinSup (Open f1 l1 r1) (Open f2 l2 r2) = Open (f1 \/ f2) (l1 \/ l2) (r1 /\ r2)

meetSup :: Lattice a => Sup a -> Sup a -> Sup a
meetSup (Open f1 l1 r1) (Open f2 l2 r2) = Open (f1 /\ f2) (l1 /\ l2) (r1 \/ r2)

instance (Finite a, Lattice a) => Lattice (Sup a)
instance (Finite a, Bounded a) => Bounded (Sup a)

{- 

instance (Finite a, Bounded a) => Heyting (Sup a)
instance (Finite a, Bounded a) => Heyting (Sup a)

instance (Finite a, Bounded a) => Heyting (Inf a) where
  neg (Predicate f) = Predicate $ \a -> neg (f a)
  (Predicate f) <=> (Predicate g) = Predicate $ \a -> f a <=> g a

instance (Finite a, Bounded a) => Quantale (Meet (Inf a)) where
  (\\) = liftA2 impliesOpen
  (//) = flip (\\)

instance (Finite a, Bounded a) => Quantale (Meet (Sup a)) where
  (\\) = liftA2 impliesOpen
  (//) = flip (\\)

negOpen (Open f x) = Open $ \a -> neg (f a)
iffOpen (Open f x) (Open g x) = Open $ \a -> f a <=> g a

impliesOpen :: Bounded a => Open t a -> Open t a -> Open t a
impliesOpen (Open f x) (Open g y) = Open (\a -> f a <= g a) (if x > y then y else top)
-}
