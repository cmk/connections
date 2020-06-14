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
  , set
  , base
  , member
  , valid
  -- ** The /Sup/ topology
  , Sup 
  , mapl
  , lower
  , lower'
  , openl
  -- ** The /Inf/ topology
  , Inf
  , mapr
  , upper
  , upper'
  , openr
) where

import safe Control.Applicative (liftA2)
import safe Data.Connection.Type
import safe Data.Connection.Int
import safe Data.Connection.Word
import safe Data.Connection.Float
import safe Data.Connection.Double
import safe Data.Connection.Ratio
import safe Data.Functor.Identity
import safe Data.Functor.Rep 
import safe Data.Foldable (foldl')
import safe Data.Semigroup.Join
import safe Data.Semigroup.Quantale
import safe Data.Lattice
import safe Data.Lattice.Heyting
import safe Data.Order
import safe Data.Order.Extended
import safe Data.Order.Interval
import safe Data.Word
import safe Data.Int
import safe Data.Universe.Class (Finite(..))
import safe Foreign.C.Types
import safe Numeric.Natural
import safe Prelude hiding (Bounded, Ord(..))
import safe qualified Control.Category as C

-- | Left and right < https://en.wikipedia.org/wiki/Alexandrov_topology Alexandrov topologies >.
data Topology = L | R

-- | An open set in the separated left or right Alexandrov topology
-- 
data Open (t :: Topology) a = Open (a -> Bool) a -- todo hide constructor

set :: Open t a -> a -> Bool
set (Open f _) = f

base :: Open t a -> a
base (Open _ x) = x

member :: a -> Open t a -> Bool
member x (Open f _) = f x

valid :: Open t a -> Bool
valid (Open f x) = f x

---------------------------------------------------------------------
-- Sup
---------------------------------------------------------------------

type Sup = Open 'L

-- | Map contra-variantly over a /Sup/ with a connection.
--
-- >>> check $ mapl (tripl f64f32) $ lower pi
-- True
-- 
mapl :: Conn a b -> Sup b -> Sup a
mapl (Conn f g) (Open o a) = Open (o . f) (g a)

-- | Create a primitive open set in the sup-topology.
--
lower :: Preorder a => a -> Sup a
lower x = Open (down x) x

-- | Augment an open set with the anti-ideal of /a/.
--
-- >>> p = lower pi :: Sup Double
-- >>> p' = lower' (0/0) p
-- >>> member (-1/0) p
-- True
-- >>> member (-1/0) p'
-- False
--
lower' :: Preorder a => a -> Sup a -> Sup a
lower' a p@(Open f x) = if up' x a then Open (f /\ down' a) x else p

-- | Create a generic open set in the sup-topology.
--
-- The first argument is the base point of the set.
--
openl :: (Preorder a, Foldable f) => a -> f a -> Sup a
openl a as = foldl' (flip lower') (lower a) as

type Set a = a -> Bool

-- Up-set ideals
up :: Preorder a => a -> Set a
up a = (a <~)

-- Up-set anti-ideals
up' :: Preorder a => a -> Set a
up' a = fmap not (a <~)

-- Down-set ideals
down :: Preorder a => a -> Set a
down a = (<~ a)

-- Down-set anti-ideals
down' :: Preorder a => a -> Set a
down' a = fmap not (<~ a)

---------------------------------------------------------------------
-- Inf
---------------------------------------------------------------------

type Inf = Open 'R

-- | Map covariantly over an /Inf/ with a connection.
--
-- >>> check $ mapr (tripr f64f32) $ upper pi
-- True
--
mapr :: Conn a b -> Inf a -> Inf b
mapr (Conn f g) (Open o a) = Open (o . g) (f a)

-- | Create a primitive open set in the inf-topology.
--
upper :: Preorder a => a -> Inf a
upper x = Open (up x) x

-- | Augment an open set with the anti-filter of /a/.
--
-- >>> p = upper pi :: Inf Double
-- >>> p' = upper' (0/0) p
-- >>> member (1/0) p
-- True
-- >>> member (1/0) p'
-- False
--
upper' :: Preorder a => a -> Inf a -> Inf a
upper' a p@(Open f x) = if down' x a then Open (f /\ up' a) x else p


-- | Create a generic open set in the inf-topology.
--
-- The first argument is the base point of the set.
--
openr :: (Preorder a, Foldable f) => a -> f a -> Inf a
openr a as = foldl' (flip upper') (upper a) as

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

instance Finite a => Preorder (Open t a) where
  pcompare (Open f _) (Open g _) = pcompare f g

instance Semigroup (Meet a) => Semigroup (Join (Inf a)) where
  (<>) = liftA2 joinInf

instance (Preorder a, Monoid (Meet a)) => Monoid (Join (Inf a)) where
  mempty = pure $ upper top

instance Semigroup (Join a) => Semigroup (Join (Sup a)) where
  (<>) = liftA2 joinSup

instance (Preorder a, Monoid (Join a)) => Monoid (Join (Sup a)) where
  mempty = pure $ lower bottom

instance Semigroup (Join a) => Semigroup (Meet (Inf a)) where
  (<>) = liftA2 meetInf

instance (Preorder a, Monoid (Join a)) => Monoid (Meet (Inf a)) where
  mempty = pure $ upper bottom

instance Semigroup (Meet a) => Semigroup (Meet (Sup a)) where
  (<>) = liftA2 meetSup

instance (Preorder a, Monoid (Meet a)) => Monoid (Meet (Sup a)) where
  mempty = pure $ lower top

instance (Finite a, Lattice a) => Lattice (Inf a)
instance (Finite a, Lattice a) => Lattice (Sup a)
instance (Finite a, Bounded a) => Bounded (Inf a)
instance (Finite a, Bounded a) => Bounded (Sup a)
instance (Finite a, Bounded a) => Distributive (Inf a)
instance (Finite a, Bounded a) => Distributive (Sup a)

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

joinInf :: Semigroup (Meet a) => Inf a -> Inf a -> Inf a
joinInf (Open f x) (Open g y) = Open (f \/ g) (x /\ y)

joinSup :: Semigroup (Join a) => Sup a -> Sup a -> Sup a
joinSup (Open f x) (Open g y) = Open (f \/ g) (x \/ y)

meetInf :: Semigroup (Join a) => Inf a -> Inf a -> Inf a
meetInf (Open f x) (Open g y) = Open (f /\ g) (x \/ y)

meetSup :: Semigroup (Meet a) => Sup a -> Sup a -> Sup a
meetSup (Open f x) (Open g y) = Open (f /\ g) (x /\ y)


