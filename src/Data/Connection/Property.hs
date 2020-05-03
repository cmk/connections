{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
module Data.Connection.Property where

import Data.Prd hiding ((~~))
import Data.Prd.Property
import Data.Connection
import Prelude hiding (Num(..),Ord(..))

-- | \( \forall x, y : f \dashv g \Rightarrow f (x) \leq y \Leftrightarrow x \leq g (y) \)
--
-- A Galois connection. This is a required property.
--
connection :: Prd a => Prd b => Conn a b -> a -> b -> Bool
connection (Conn f g) = adjoint (<=) (<=) f g

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
closed :: Prd a => Prd b => Conn a b -> a -> Bool
closed (Conn f g) = invertible (>=) f g

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
closed' :: Prd a => Prd b => Trip a b -> a -> Bool
closed' t x = closed (tripl t) x && kernel (tripr t) x

-- | \( \forall x : f \dashv g \Rightarrow f \circ g (x) \leq x \)
--
-- This is a required property.
--
kernel :: Prd a => Prd b => Conn a b -> b -> Bool
kernel (Conn f g) = invertible (<=) g f

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
kernel' :: Prd a => Prd b => Trip a b -> b -> Bool
kernel' t x = closed (tripr t) x && kernel (tripl t) x

-- | \( \forall x, y : x \leq y \Rightarrow g (x) \leq g (y) \)
--
-- This is a required property.
--
monotoner :: Prd a => Prd b => Conn a b -> b -> b -> Bool
monotoner (Conn _ g) = monotone (<=) (<=) g

-- | \( \forall x, y : x \leq y \Rightarrow f (x) \leq f (y) \)
--
-- This is a required property.
--
monotonel :: Prd a => Prd b => Conn a b -> a -> a -> Bool
monotonel (Conn f _) = monotone (<=) (<=) f

-- | \( \forall x : f \dashv g \Rightarrow unit \circ unit (x) \sim unit (x) \)
--
-- This is a required property.
--
idempotent_unit :: Prd a => Prd b => Conn a b -> a -> Bool
idempotent_unit conn = idempotent (=~) $ unit conn

-- | \( \forall x : f \dashv g \Rightarrow counit \circ counit (x) \sim counit (x) \)
--
-- This is a required property.
--
idempotent_counit :: Prd a => Prd b => Conn a b -> b -> Bool
idempotent_counit conn = idempotent (=~) $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow counit \circ f (x) \sim f (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectivel :: Prd a => Prd b => Conn a b -> a -> Bool
projectivel conn@(Conn f _) = projective (=~) f $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow unit \circ g (x) \sim g (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectiver :: Prd a => Prd b => Conn a b -> b -> Bool
projectiver conn@(Conn _ g) = projective (=~) g $ unit conn

---------------------------------------------------------------------
-- Properties of general relations
---------------------------------------------------------------------

-- | \( \forall a, b: a \leq b \Rightarrow f(a) \leq f(b) \)
--
monotone :: Rel r Bool -> Rel s Bool -> (r -> s) -> Rel r Bool
monotone (#) (%) f a b = a # b ==> f a % f b

-- | \( \forall a, b: a \leq b \Rightarrow f(b) \leq f(a) \)
--
antitone :: Rel r Bool -> Rel s Bool -> (r -> s) -> Rel r Bool
antitone (#) (%) f a b = a # b ==> f b % f a

-- | \( \forall a: f a \# b \Leftrightarrow a \# g b \)
--
-- For example, a Galois connection is defined by @adjoint (<=)@.
--
adjoint :: Rel r Bool -> Rel s Bool -> (s -> r) -> (r -> s) -> (s -> r -> Bool)
adjoint (#) (%) f g a b = f a # b <==> a % g b

-- | \( \forall a: f (g a) \sim a \)
--
invertible :: Rel s b -> (s -> r) -> (r -> s) -> (s -> b)
invertible (~~) f g a = g (f a) ~~ a

-- | \( \forall a: g \circ f (a) \sim f (a) \)
--
projective :: Rel s b -> (r -> s) -> (s -> s) -> r -> b
projective (~~) f g r = g (f r) ~~ f r

-- | \( \forall a: f \circ f(a) \sim f(a) \)
--
idempotent :: Rel r b -> (r -> r) -> r -> b
idempotent (~~) f = projective (~~) f f
