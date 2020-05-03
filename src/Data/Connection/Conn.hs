{-# Language TypeFamilies        #-}
{-# Language TypeApplications    #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ConstraintKinds     #-}
{-# Language Safe                #-}
module Data.Connection.Conn (
  -- * Connection
    Conn(..)
  , connl
  , connr
  , mapl
  , mapr
  , map2l
  , map2r
  , unit
  , counit
  , dual
  , strong
  , choice
) where

import safe Control.Category (Category, (>>>))
import safe Data.Bifunctor (bimap)
import safe Data.Bool
import safe Data.Prd
import safe Data.Prd.Nan
import safe Data.Prd.Top
import safe Prelude hiding (Ord, Bounded)
import safe qualified Control.Category as C

-- | A Galois connection between two monotone functions.
--
-- A Galois connection between /f/ and /g/, written \(f \dashv g \)
-- is an adjunction in the category of preorders.
--
-- Each side of the connection may be defined in terms of the other:
-- 
--  \( g(x) = \sup \{y \in E \mid f(y) \leq x \} \)
--
--  \( f(x) = \inf \{y \in E \mid g(y) \geq x \} \)
--
-- For further information see 'Data.Connection.Property' and <https://ncatlab.org/nlab/show/Galois+connection>.
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

-- | Map over a connection from the left.
--
mapl :: Conn a b -> (a -> a) -> b -> b
mapl (Conn f g) h b = f $ h (g b)

-- | Map over a connection from the right.
--
mapr :: Conn a b -> (b -> b) -> a -> a
mapr (Conn f g) h a = g $ h (f a)

-- | Zip over a connection from the left.
--
map2l :: Conn a b -> (a -> a -> a) -> b -> b -> b
map2l (Conn f g) h b1 b2 = f $ h (g b1) (g b2)

-- | Zip over a connection from the right.
--
map2r :: Conn a b -> (b -> b -> b) -> a -> a -> a
map2r (Conn f g) h a1 a2 = g $ h (f a1) (f a2)

-- | Round trip through a connection.
--
-- > x <= unit x
--
unit :: Conn a b -> a -> a
unit c = mapr c id

-- | Reverse round trip through a connection.
--
-- > counit x <= x
--
counit :: Conn a b -> b -> b
counit c = mapl c id

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
