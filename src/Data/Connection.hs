{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}

module Data.Connection (
  -- * Connection
    Conn(..)
  , connl
  , connr
  , unit
  , counit
  , pcomparing
  , dual
  , first
  , second
  , left
  , right
  , strong
  , choice
  , just
  , list
  , ordbin
  , binord
  -- * Triple
  , Trip(..)
  , tripl
  , tripr
  , unitl
  , unitr
  , counitl
  , counitr
  , trivial
  , first'
  , second'
  , left'
  , right'
  , strong'
  , choice'
  , maybel
  , mayber
) where


import Control.Category (Category, (>>>))
import Data.Bifunctor (bimap)
import Data.Bool
import Data.Prd
import Prelude hiding (Ord, Bounded)

import qualified Control.Category as C


-- | A Galois connection between two monotone functions.
--
-- /Caution/: Monotonicity is not checked.
--
-- Each side of the connection may be defined in terms of the other:
-- 
--  \( connr(x) = \sup \{y \in E \mid connl(y) \leq x \} \)
--
--  \( connl(x) = \inf \{y \in E \mid connr(y) \geq x \} \)
--
-- Galois connections have the same properties as adjunctions defined over other categories:
--
--  \( \forall x, y : connl \dashv connr \Rightarrow connl (x) \leq b \Leftrightarrow x \leq connr (y) \)
--
--  \( \forall x, y : x \leq y \Rightarrow connl (x) \leq connl (y) \)
--
--  \( \forall x, y : x \leq y \Rightarrow connr (x) \leq connr (y) \)
--
--  \( \forall x : connl \dashv connr \Rightarrow x \leq connr \circ connl (x) \)
--
--  \( \forall x : connl \dashv connr \Rightarrow connl \circ connr (x) \leq x \)
--
--  \( \forall x : unit \circ unit (x) \sim unit (x) \)
--
--  \( \forall x : counit \circ counit (x) \sim counit (x) \)
--
--  \( \forall x : counit \circ connl (x) \sim connl (x) \)
--
--  \( \forall x : unit \circ connr (x) \sim connr (x) \)
--
-- See also 'Data.Function.Connection.Property' and <https://en.wikipedia.org/wiki/Galois_connection>.
--
data Conn a b = Conn (a -> b) (b -> a)

instance Category Conn where
  id = Conn id id
  Conn f' g' . Conn f g = Conn (f' . f) (g . g')

-- | Extract the left side of a connection.
--
connl :: Prd a => Prd b => Conn a b -> a -> b
connl (Conn f _) = f

-- | Extract the right side of a connection.
--
connr :: Prd a => Prd b => Conn a b -> b -> a
connr (Conn _ g) = g

-- | Round trip through a connection.
--
-- @x '<=' 'unit' x@
--
unit :: Prd a => Prd b => Conn a b -> a -> a
unit (Conn f g) = g . f

-- | Reverse round trip through a connection.
--
-- @'counit' x '<=' x@
--
counit :: Prd a => Prd b => Conn a b -> b -> b
counit (Conn f g) = f . g

-- | Partial version of 'Data.Ord.comparing'. 
--
pcomparing :: Prd a => Prd b => Conn a b -> a -> a -> Maybe Ordering
pcomparing (Conn f _) x y = f x `pcompare` f y

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- | Reverse a connection using the dual partial order on each side.
--
dual :: Prd a => Prd b => Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down b) -> Down $ g b) (\(Down a) -> Down $ f a)

-- | @'first' (ab '>>>' cd) = 'first' ab '>>>' 'first' cd@
--
first :: Prd a => Prd b => Prd c => Conn a b -> Conn (a, c) (b, c)
first = flip strong C.id

-- | @'second' (ab '>>>' cd) = 'second' ab '>>>' 'second' cd@
--
second :: Prd a => Prd b => Prd c => Conn a b -> Conn (c, a) (c, b)
second = strong C.id

-- | @'left' (ab '>>>' cd) = 'left' ab '>>>' 'left' cd@
--
left :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either a c) (Either b c)
left = flip choice C.id

-- | @'right' (ab '>>>' cd) = 'right' ab '>>>' 'right' cd@
--
right :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either c a) (Either c b)
right = choice C.id 

strong :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn (bimap ab cd) (bimap ba dc)

choice :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)

just :: Prd a => Prd b => Conn a b -> Conn (Maybe a) (Maybe b)
just (Conn f g) = Conn (fmap f) (fmap g)

list :: Prd a => Prd b => Conn a b -> Conn [a] [b]
list (Conn f g) = Conn (fmap f) (fmap g)

ordbin :: Conn Ordering Bool
ordbin = Conn f g where
  f GT = True
  f _  = False

  g True = GT
  g _    = EQ

binord :: Conn Bool Ordering
binord = Conn f g where
  f False = LT
  f _     = EQ

  g LT = False
  g _  = True

---------------------------------------------------------------------
-- Adjoint triples
---------------------------------------------------------------------

-- | An adjoint triple.
--
-- @'Trip' f g h@ satisfies:
--
-- @
-- f ⊣ g
-- ⊥   ⊥
-- g ⊣ h
-- @
--
-- See <https://ncatlab.org/nlab/show/adjoint+triple>
--
data Trip a b = Trip (a -> b) (b -> a) (a -> b)

instance Category Trip where
  id = Trip id id id
  Trip f' g' h' . Trip f g h = Trip (f' . f) (g . g') (h' . h)

tripl :: Prd a => Prd b => Trip a b -> Conn a b
tripl (Trip f g _) = Conn f g

tripr :: Prd a => Prd b => Trip a b -> Conn b a
tripr (Trip _ g h) = Conn g h

unitl :: Prd a => Prd b => Trip a b -> a -> a
unitl = unit . tripl

unitr :: Prd a => Prd b => Trip a b -> b -> b
unitr = unit . tripr

counitl :: Prd a => Prd b => Trip a b -> b -> b
counitl = counit . tripl

counitr :: Prd a => Prd b => Trip a b -> a -> a
counitr = counit . tripr

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

trivial :: Prd a => Bounded a => Trip () a
trivial = Trip (const minimal) (const ()) (const maximal)

first' :: Prd a => Prd b => Prd c => Trip a b -> Trip (a, c) (b, c)
first' = flip strong' C.id

second' :: Prd a => Prd b => Prd c => Trip a b -> Trip (c, a) (c, b)
second' = strong' C.id

left' :: Prd a => Prd b => Prd c => Trip a b -> Trip (Either a c) (Either b c)
left' = flip choice' C.id

right' :: Prd a => Prd b => Prd c => Trip a b -> Trip (Either c a) (Either c b)
right' = choice' C.id

strong' :: Prd a => Prd b => Prd c => Prd d => Trip a b -> Trip c d -> Trip (a, c) (b, d)
strong' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

choice' :: Prd a => Prd b => Prd c => Prd d => Trip a b -> Trip c d -> Trip (Either a c) (Either b d)
choice' (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

maybel :: Prd a => Bounded b => Trip (Maybe a) (Either a b)
maybel = Trip f g h where
  f = maybe (Right minimal) Left
  g = either Just (const Nothing)
  h = maybe (Right maximal) Left

mayber :: Prd b => Bounded a => Trip (Maybe b) (Either a b)
mayber = Trip f g h where
  f = maybe (Left minimal) Right
  g = either (const Nothing) Just
  h = maybe (Left maximal) Right
