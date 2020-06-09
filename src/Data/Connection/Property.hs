{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language ConstraintKinds #-}
-- | Galois connections have the same properties as adjunctions defined over other categories:
--
--  \( \forall x, y : f \dashv g \Rightarrow f (x) \leq b \Leftrightarrow x \leq g (y) \)
--
--  \( \forall x, y : x \leq y \Rightarrow f (x) \leq f (y) \)
--
--  \( \forall x, y : x \leq y \Rightarrow g (x) \leq g (y) \)
--
--  \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
--  \( \forall x : f \dashv g \Rightarrow f \circ g (x) \leq x \)
--
--  \( \forall x : unit \circ unit (x) \sim unit (x) \)
--
--  \( \forall x : counit \circ counit (x) \sim counit (x) \)
--
--  \( \forall x : counit \circ f (x) \sim f (x) \)
--
--  \( \forall x : unit \circ g (x) \sim g (x) \)
--
module Data.Connection.Property where

import Data.Order
import Data.Order.Property
import Data.Lattice.Heyting
import Data.Connection.Type
import Prelude hiding (Num(..),Ord(..))

-- | \( \forall x, y : f \dashv g \Rightarrow f (x) \leq y \Leftrightarrow x \leq g (y) \)
--
-- A Galois connection is an adjunction of preorders. This is a required property.
--
adjoint :: Preorder a => Preorder b => Conn a b -> a -> b -> Bool
adjoint (Conn f g) a b = f a <~ b <=> a <~ g b

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
closed :: Preorder a => Preorder b => Conn a b -> a -> Bool
closed (Conn f g) = invertible (>~) f g

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
closed' :: Preorder a => Preorder b => Trip a b -> a -> Bool
closed' t x = closed (tripl t) x && kernel (tripr t) x

-- | \( \forall x : f \dashv g \Rightarrow f \circ g (x) \leq x \)
--
-- This is a required property.
--
kernel :: Preorder a => Preorder b => Conn a b -> b -> Bool
kernel (Conn f g) = invertible (<~) g f

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
kernel' :: Preorder a => Preorder b => Trip a b -> b -> Bool
kernel' t x = closed (tripr t) x && kernel (tripl t) x

-- | \( \forall x, y : x \leq y \Rightarrow f (x) \leq f (y) \)
--
-- This is a required property.
--
monotoneL :: Preorder a => Preorder b => Conn a b -> a -> a -> Bool
monotoneL (Conn f _) = monotone (<~) (<~) f

-- | \( \forall x, y : x \leq y \Rightarrow g (x) \leq g (y) \)
--
-- This is a required property.
--
monotoneR :: Preorder a => Preorder b => Conn a b -> b -> b -> Bool
monotoneR (Conn _ g) = monotone (<~) (<~) g

-- | \( \forall x : f \dashv g \Rightarrow unit \circ unit (x) \sim unit (x) \)
--
-- This is a required property.
--
idempotent_unit :: Preorder a => Preorder b => Conn a b -> a -> Bool
idempotent_unit conn = idempotent (~~) $ unit conn

-- | \( \forall x : f \dashv g \Rightarrow counit \circ counit (x) \sim counit (x) \)
--
-- This is a required property.
--
idempotent_counit :: Preorder a => Preorder b => Conn a b -> b -> Bool
idempotent_counit conn = idempotent (~~) $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow counit \circ f (x) \sim f (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectiveL :: Preorder a => Preorder b => Conn a b -> a -> Bool
projectiveL conn@(Conn f _) = projective (~~) f $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow unit \circ g (x) \sim g (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectiveR :: Preorder a => Preorder b => Conn a b -> b -> Bool
projectiveR conn@(Conn _ g) = projective (~~) g $ unit conn

---------------------------------------------------------------------
-- Properties of general relations
---------------------------------------------------------------------

-- | \( \forall a, b: a \leq b \Rightarrow f(a) \leq f(b) \)
--
monotone :: Rel r Bool -> Rel s Bool -> (r -> s) -> Rel r Bool
monotone (#) (%) f a b = a # b ==> f a % f b

-- | \( \forall a, b: a \leq b \Rightarrow f(b) \leq f(a) \)
--
--antitone :: Rel r Bool -> Rel s Bool -> (r -> s) -> Rel r Bool
--antitone (#) (%) f a b = a # b ==> f b % f a

-- | \( \forall a: f a \leq b \Leftrightarrow a \leq g b \)
--
-- For example, a Galois connection is defined by @adjoint (<~)@.
--
--adjoint :: Rel r Bool -> Rel s Bool -> (s -> r) -> (r -> s) -> (s -> r -> Bool)
--adjoint (#) (%) f g a b = f a # b <~> a % g b

-- | \( \forall a: f (g a) \sim a \)
--
invertible :: Rel s b -> (s -> r) -> (r -> s) -> (s -> b)
invertible (#) f g a = g (f a) # a

-- | \( \forall a: g \circ f (a) \sim f (a) \)
--
projective :: Rel s b -> (r -> s) -> (s -> s) -> r -> b
projective (#) f g r = g (f r) # f r

-- | \( \forall a: f \circ f(a) \sim f(a) \)
--
idempotent :: Rel r b -> (r -> r) -> r -> b
idempotent (#) f = projective (#) f f
