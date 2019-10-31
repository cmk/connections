{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}

module Data.Connection (

  -- * Connection
    Conn(..)
  , connl
  , connr
  , unit
  , counit
  , pcomparing
  , dual
  , (***)
  , (+++)
  , (&&&)
  , (|||)
  , _1
  , _2
  , _L
  , _R
  , just
  , list
  , binord
  , ordbin

  -- * Triple
  , Trip(..)
  , tripl
  , tripr
  , unitl
  , unitr
  , counitl
  , counitr
  , ceiling'
  , floor'
  , (****)
  , (++++)
  , (&&&&)
  , (||||)
  , _1'
  , _2'
  , _L'
  , _R'
  , diag
  , codiag
  , bound
  , maybel
  , mayber
) where

import Control.Category (Category, (>>>))
import Data.Bifunctor (bimap)
import Data.Word
import Data.Int
import Data.Prd
import Data.Prd.Lattice
import Data.Ord (Down(..))
import Prelude 

import qualified Data.Ord as O
import qualified Control.Category as C


infixr 3 ***, ****, &&&, &&&&
infixr 2 +++, ++++, |||, ||||

-- | A Galois connection between two monotone functions: \(connl \dashv connr \)
--
-- Each side of the adjunction may be defined in terms of the other:
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

connl :: Prd a => Prd b => Conn a b -> a -> b
connl (Conn f _) = f

connr :: Prd a => Prd b => Conn a b -> b -> a
connr (Conn _ g) = g

-- @x <~ unit x@
unit :: Prd a => Prd b => Conn a b -> a -> a
unit (Conn f g) = g . f

-- @counit x <~ x@
counit :: Prd a => Prd b => Conn a b -> b -> b
counit (Conn f g) = f . g

-- | Partial version of 'Data.Ord.comparing'. 
--
-- Helpful in conjunction with the @xxxBy@ functions from 'Data.List'.
--
pcomparing :: Eq b => Prd a => Prd b => Conn a b -> a -> a -> Maybe Ordering
pcomparing (Conn f _) x y = f x `pcompare` f y

instance Category Conn where
  id = Conn id id
  Conn f' g' . Conn f g = Conn (f' . f) (g . g')

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

dual :: Prd a => Prd b => Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down b) -> Down $ g b) (\(Down a) -> Down $ f a)

(***) :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (a, c) (b, d)
(***) (Conn ab ba) (Conn cd dc) = Conn f g where
  f = bimap ab cd 
  g = bimap ba dc

(+++) :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
(+++) (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)

(&&&) :: Prd a => Prd b => Lattice c => Conn c a -> Conn c b -> Conn c (a, b)
f &&& g = tripr diag >>> f *** g

(|||) :: Prd a => Prd b => Prd c => Conn a c -> Conn b c -> Conn (Either a b) c
f ||| g = f +++ g >>> tripr codiag

-- | Lens into first part of a product.
--
-- @'_1' (ab >>> cd) = '_1' ab >>> '_1' cd@
--
_1 :: Prd a => Prd b => Prd c => Conn a b -> Conn (a, c) (b, c)
_1 = (*** C.id)

_2 :: Prd a => Prd b => Prd c => Conn a b -> Conn (c, a) (c, b)
_2 = (C.id ***)

-- | Prism into left part of a sum.
--
-- @'_L' (ab >>> cd) = '_L' ab >>> '_L' cd@
--
_L :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either a c) (Either b c)
_L = (+++ C.id)

_R :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either c a) (Either c b)
_R = (C.id +++)

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
--  'Trip'
---------------------------------------------------------------------

-- | An adjoint triple.
--
-- @'Trip' f g h@ satisfies:
--
-- f ⊣ g
-- ⊥   ⊥
-- g ⊣ h
--
-- See <https://ncatlab.org/nlab/show/adjoint+triple>
--
data Trip a b = Trip (a -> b) (b -> a) (a -> b)

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

ceiling' :: Prd a => Prd b => Trip a b -> a -> b
ceiling' = connl . tripl

floor' :: Prd a => Prd b => Trip a b -> a -> b
floor' = connr . tripr

instance Category Trip where
  id = Trip id id id
  Trip f' g' h' . Trip f g h = Trip (f' . f) (g . g') (h' . h)

---------------------------------------------------------------------
--  Instances
---------------------------------------------------------------------

(****) :: Prd a => Prd b => Prd c => Prd d => Trip a b -> Trip c d -> Trip (a, c) (b, d)
(****) (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = bimap ab cd 
  g = bimap ba dc
  h = bimap ab' cd'

(++++) :: Prd a => Prd b => Prd c => Prd d => Trip a b -> Trip c d -> Trip (Either a c) (Either b d)
(++++) (Trip ab ba ab') (Trip cd dc cd') = Trip f g h where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)
  h = either (Left . ab') (Right . cd')

(&&&&) :: Prd a => Prd b => Lattice c => Trip a c -> Trip b c -> Trip (a, b) c
f &&&& g = f **** g >>> diag

(||||) :: Prd a => Prd b => Prd c => Trip c a -> Trip c b -> Trip c (Either a b)
(||||) f g = codiag >>> f ++++ g

_1' :: Prd a => Prd b => Prd c => Trip a b -> Trip (a, c) (b, c)
_1' = (**** C.id)

_2' :: Prd a => Prd b => Prd c => Trip a b -> Trip (c, a) (c, b)
_2' = (C.id ****)

_L' :: Prd a => Prd b => Prd c => Trip a b -> Trip (Either a c) (Either b c)
_L' = (++++ C.id)

_R' :: Prd a => Prd b => Prd c => Trip a b -> Trip (Either c a) (Either c b)
_R' = (C.id ++++)

diag :: Lattice a => Trip (a, a) a
diag = Trip (uncurry (\/)) (\x -> (x,x)) (uncurry (/\))

codiag :: Prd a => Trip a (Either a a)
codiag = Trip Left (either id id) Right

bound :: Prd a => Bound a => Trip () a
bound = Trip (const minimal) (const ()) (const maximal)

maybel :: Prd a => Bound b => Trip (Maybe a) (Either a b)
maybel = Trip f g h where
  f = maybe (Right minimal) Left
  g = either Just (const Nothing)
  h = maybe (Right maximal) Left

mayber :: Prd b => Bound a => Trip (Maybe b) (Either a b)
mayber = Trip f g h where
  f = maybe (Left minimal) Right
  g = either (const Nothing) Just
  h = maybe (Left maximal) Right
