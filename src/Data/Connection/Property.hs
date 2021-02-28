{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

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
module Data.Connection.Property (
  -- * Adjointness
  adjointL,
  adjointR,
  adjoint,
  adjunction,
  -- * Closure
  closedL,
  closedR,
  closed,
  kernelL,
  kernelR,
  kernel,
  invertible,
  -- * Monotonicity
  monotonicR,
  monotonicL,
  monotonic,
  monotone,
  -- * Idempotence
  idempotentL,
  idempotentR,
  idempotent,
  projective,
) where

import Data.Connection
import Data.Order
import Data.Order.Property
import Prelude hiding (Num (..), Ord (..), ceiling, floor)

-- Adjointness

-------------------------

-- | \( \forall x, y : f \dashv g \Rightarrow f (x) \leq y \Leftrightarrow x \leq g (y) \)
--
-- A Galois connection is an adjunction of preorders. This is a required property.
adjointL :: (Preorder a, Preorder b) => ConnL a b -> a -> b -> Bool
adjointL (ConnL f g) = adjunction (<~) (<~) f g

adjointR :: (Preorder a, Preorder b) => ConnR a b -> a -> b -> Bool
adjointR (ConnR f g) = adjunction (>~) (>~) g f

adjoint :: (Preorder a, Preorder b) => ConnK a b -> a -> b -> Bool
adjoint t a b =
    adjointL t a b
        && adjointR t a b
        && adjointL (swapL t) b a
        && adjointR (swapR t) b a

-- | \( \forall a: f a \leq b \Leftrightarrow a \leq g b \)
--
-- A monotone Galois connection is defined by @adjunction (<~) (<~)@,
-- while an antitone Galois connection is defined by @adjunction (>~) (<~)@.
adjunction :: Rel r Bool -> Rel s Bool -> (s -> r) -> (r -> s) -> s -> r -> Bool
adjunction (#) (%) f g a b = f a # b <=> a % g b

-- Closure

-------------------------

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
closedL :: (Preorder a, Preorder b) => ConnL a b -> a -> Bool
closedL (ConnL f g) = invertible (>~) f g

closedR :: (Preorder a, Preorder b) => ConnR a b -> a -> Bool
closedR (ConnR f g) = invertible (<~) g f

closed :: (Preorder a, Preorder b) => ConnK a b -> a -> Bool
closed t a = closedL t a && closedR t a

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
kernelL :: (Preorder a, Preorder b) => ConnL a b -> b -> Bool
kernelL (ConnL f g) = invertible (<~) g f

kernelR :: (Preorder a, Preorder b) => ConnR a b -> b -> Bool
kernelR (ConnR f g) = invertible (>~) f g

kernel :: (Preorder a, Preorder b) => ConnK a b -> b -> Bool
kernel t b = kernelL t b && kernelR t b

-- | \( \forall a: f (g a) \sim a \)
invertible :: Rel s b -> (s -> r) -> (r -> s) -> s -> b
invertible (#) f g a = g (f a) # a

-- Monotonicity

-------------------------

-- | \( \forall x, y : x \leq y \Rightarrow f (x) \leq f (y) \)
--
-- This is a required property.
monotonicR :: (Preorder a, Preorder b) => ConnR a b -> a -> a -> b -> b -> Bool
monotonicR (ConnR f g) a1 a2 b1 b2 = monotone (<~) (<~) g a1 a2 && monotone (<~) (<~) f b1 b2

monotonicL :: (Preorder a, Preorder b) => ConnL a b -> a -> a -> b -> b -> Bool
monotonicL (ConnL f g) a1 a2 b1 b2 = monotone (<~) (<~) f a1 a2 && monotone (<~) (<~) g b1 b2

monotonic :: (Preorder a, Preorder b) => ConnK a b -> a -> a -> b -> b -> Bool
monotonic t a1 a2 b1 b2 = monotonicL t a1 a2 b1 b2 && monotonicR t a1 a2 b1 b2

-- | \( \forall a, b: a \leq b \Rightarrow f(a) \leq f(b) \)
monotone :: Rel r Bool -> Rel s Bool -> (r -> s) -> r -> r -> Bool
monotone (#) (%) f a b = a # b ==> f a % f b

-- Idempotence

-------------------------

-- | \( \forall x: f \dashv g \Rightarrow counit \circ f (x) \sim f (x) \wedge unit \circ g (x) \sim g (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
idempotentL :: (Preorder a, Preorder b) => ConnL a b -> a -> b -> Bool
idempotentL c@(ConnL f g) a b = projective (~~) g (upper c) b && projective (~~) f (counit c) a

idempotentR :: (Preorder a, Preorder b) => ConnR a b -> a -> b -> Bool
idempotentR c@(ConnR f g) a b = projective (~~) g (unit c) a && projective (~~) f (lower c) b

idempotent :: (Preorder a, Preorder b) => ConnK a b -> a -> b -> Bool
idempotent t a b = idempotentL t a b && idempotentR t a b

-- | \( \forall a: g \circ f (a) \sim f (a) \)
--
projective :: Rel s b -> (r -> s) -> (s -> s) -> r -> b
projective (#) f g r = g (f r) # f r

