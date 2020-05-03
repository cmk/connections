{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds #-}

module Data.Connection.Conn (
  -- * Connection
    Conn(..)
  , connl
  , connr
  , unit
  , counit
  , dual
  , strong
  , choice
) where


import Control.Category (Category, (>>>))
import Data.Bifunctor (bimap)
import Data.Bool
import Data.Prd
import Data.Prd.Nan
import Data.Prd.Top
import Prelude hiding (Ord, Bounded)

import qualified Control.Category as C


-- | A Galois connection between two monotone functions.
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
-- See <https://ncatlab.org/nlab/show/Galois+connection>
--
-- /Caution/: Monotonicity is not checked.
--
data Conn a b = Conn (a -> b) (b -> a)

instance Category Conn where
  id = Conn id id
  Conn f' g' . Conn f g = Conn (f' . f) (g . g')

-- | Extract the left side of a connection.
--
connl :: Conn a b -> a -> b
connl (Conn f _) = f

-- | Extract the right side of a connection.
--
connr :: Conn a b -> b -> a
connr (Conn _ g) = g

-- | Round trip through a connection.
--
-- > x <= unit x
--
unit :: Conn a b -> a -> a
unit (Conn f g) = g . f

-- | Reverse round trip through a connection.
--
-- > counit x <= x
--
counit :: Conn a b -> b -> b
counit (Conn f g) = f . g

-- | Reverse a connection using the dual partial order on each side.
--
dual :: Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down b) -> Down $ g b) (\(Down a) -> Down $ f a)

-- |
--
-- > (strong id) (ab >>> cd) = (strong id) ab >>> (strong id) cd
-- > (flip strong id) (ab >>> cd) = (flip strong id) ab >>> (flip strong id) cd
--
strong :: Conn a b -> Conn c d -> Conn (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn (bimap ab cd) (bimap ba dc)

-- |
--
-- > (choice id) (ab >>> cd) = (choice id) ab >>> (choice id) cd
-- > (flip choice id) (ab >>> cd) = (flip choice id) ab >>> (flip choice id) cd
--
choice :: Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
