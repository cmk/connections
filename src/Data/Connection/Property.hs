{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
module Data.Connection.Property where

import Data.Proxy
import Data.Prd
import Data.Connection

import qualified Test.Function.Idempotent as Prop
import qualified Test.Function.Invertible as Prop
import qualified Test.Function.Monotone   as Prop

import Test.Logic
import Prelude hiding (Num(..),Ord(..))


-- | \( \forall x, y : f \dashv g \Rightarrow f (x) \leq y \Leftrightarrow x \leq g (y) \)
--
-- A monotoner Galois connection.
--
connection :: Prd a => Prd b => Conn a b -> a -> b -> Bool
connection (Conn f g) = Prop.adjoint_on (<~) (<~) f g

-- | \( \forall x : f \dashv g \Rightarrow x \leq g \circ f (x) \)
--
-- This is a required property.
--
closed :: Prd a => Prd b => Conn a b -> a -> Bool
closed (Conn f g) = Prop.invertible_on (>~) f g

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
kernel (Conn f g) = Prop.invertible_on (<~) g f

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
monotoner (Conn _ g) = Prop.monotone_on (<~) (<~) g

-- | \( \forall x, y : x \leq y \Rightarrow f (x) \leq f (y) \)
--
-- This is a required property.
--
monotonel :: Prd a => Prd b => Conn a b -> a -> a -> Bool
monotonel (Conn f _) = Prop.monotone_on (<~) (<~) f

-- | \( \forall x : f \dashv g \Rightarrow unit \circ unit (x) \sim unit (x) \)
--
idempotent_unit :: Prd a => Prd b => Conn a b -> a -> Bool
idempotent_unit conn = Prop.idempotent_on (=~) $ unit conn

-- | \( \forall x : f \dashv g \Rightarrow counit \circ counit (x) \sim counit (x) \)
--
idempotent_counit :: Prd a => Prd b => Conn a b -> b -> Bool
idempotent_counit conn = Prop.idempotent_on (=~) $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow counit \circ f (x) \sim f (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectivel :: Prd a => Prd b => Conn a b -> a -> Bool
projectivel conn@(Conn f _) = Prop.projective_on (=~) f $ counit conn

-- | \( \forall x: f \dashv g \Rightarrow unit \circ g (x) \sim g (x) \)
--
-- See <https://ncatlab.org/nlab/show/idempotent+adjunction>
--
projectiver :: Prd a => Prd b => Conn a b -> b -> Bool
projectiver conn@(Conn _ g) = Prop.projective_on (=~) g $ unit conn
