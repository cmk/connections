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
  , (|||)
  , just
  , list
  , first
  , second
  , left
  , right
  , strong
  , choice
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
  , joined
  , bound
  , maybel
  , mayber
  , first'
  , second'
  , left'
  , right'
  , strong'
  , choice'
  -- * Rounding
  , Mode(..)
  , half
  , truncateWith
  , ceilingWith
  , floorWith
  , roundWith
  , addWith
  , negWith
  , subWith
  , mulWith
  , fmaWith
  , remWith
  , divWith
) where


import Control.Category (Category, (>>>))
import Data.Bifunctor (bimap)
import Data.Bool
import Data.Word
import Data.Int
import Data.Prd
import Data.Group
import Data.Semiring
import Data.Semifield
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Prelude hiding (Ord(..), Num(..), Fractional(..), RealFrac(..))

import Test.Logic (xor, (<==>),(==>))

import qualified Data.Ord as O
import qualified Control.Category as C


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

instance Category Conn where
  id = Conn id id
  Conn f' g' . Conn f g = Conn (f' . f) (g . g')

connl :: Prd a => Prd b => Conn a b -> a -> b
connl (Conn f _) = f

connr :: Prd a => Prd b => Conn a b -> b -> a
connr (Conn _ g) = g

-- @x <= unit x@
unit :: Prd a => Prd b => Conn a b -> a -> a
unit (Conn f g) = g . f

-- @counit x <= x@
counit :: Prd a => Prd b => Conn a b -> b -> b
counit (Conn f g) = f . g

-- | Partial version of 'Data.Ord.comparing'. 
--
-- Helpful in conjunction with the @xxxBy@ functions from 'Data.List'.
--
pcomparing :: Eq b => Prd a => Prd b => Conn a b -> a -> a -> Maybe Ordering
pcomparing (Conn f _) x y = f x `pcompare` f y

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

dual :: Prd a => Prd b => Conn a b -> Conn (Down b) (Down a)
dual (Conn f g) = Conn (\(Down b) -> Down $ g b) (\(Down a) -> Down $ f a)

just :: Prd a => Prd b => Conn a b -> Conn (Maybe a) (Maybe b)
just (Conn f g) = Conn (fmap f) (fmap g)

list :: Prd a => Prd b => Conn a b -> Conn [a] [b]
list (Conn f g) = Conn (fmap f) (fmap g)

-- @'first' (ab >>> cd) = 'first' ab >>> 'first' cd@
--
first :: Prd a => Prd b => Prd c => Conn a b -> Conn (a, c) (b, c)
first = flip strong C.id

second :: Prd a => Prd b => Prd c => Conn a b -> Conn (c, a) (c, b)
second = strong C.id

-- @'left' (ab >>> cd) = 'left' ab >>> 'left' cd@
--
left :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either a c) (Either b c)
left = flip choice C.id

right :: Prd a => Prd b => Prd c => Conn a b -> Conn (Either c a) (Either c b)
right = choice C.id 

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

forked :: JoinSemilattice a => MeetSemilattice a => Trip (a, a) a
forked = Trip (uncurry (∨)) (\x -> (x,x)) (uncurry (∧))

joined :: Prd a => Trip a (Either a a)
joined = Trip Left (either id id) Right

(&&&) :: Prd a => Prd b => JoinSemilattice c => MeetSemilattice c => Conn c a -> Conn c b -> Conn c (a, b)
f &&& g = tripr forked >>> f `strong` g

(|||) :: Prd a => Prd b => Prd c => Conn a c -> Conn b c -> Conn (Either a b) c
f ||| g = f `choice` g >>> tripr joined

strong :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (a, c) (b, d)
strong (Conn ab ba) (Conn cd dc) = Conn f g where
  f = bimap ab cd 
  g = bimap ba dc

choice :: Prd a => Prd b => Prd c => Prd d => Conn a b -> Conn c d -> Conn (Either a c) (Either b d)
choice (Conn ab ba) (Conn cd dc) = Conn f g where
  f = either (Left . ab) (Right . cd)
  g = either (Left . ba) (Right . dc)

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

---------------------------------------------------------------------
-- Rounding
---------------------------------------------------------------------

-- | The four primary IEEE rounding modes.
--
-- See <https://en.wikipedia.org/wiki/Rounding>.
--
data Mode = 
    RNZ -- ^ round to nearest with ties towards zero
  | RTP -- ^ round towards pos infinity
  | RTN -- ^ round towards neg infinity
  | RTZ -- ^ round towards zero
  deriving (Eq, Show, Read, Enum, Bounded)

-- | Determine which half of the interval between two representations of /a/ a particular value lies.
-- 
half :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Maybe Ordering
half t x = pcompare (x - unitl t x) (counitr t x - x) 

-- | Determine whether /x/ lies above the halfway point between two representations.
-- 
-- @ 'above' t x '==' (x '-' 'unitl' t x) '`gt`' ('counitr' t x '-' x) @
--
above :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
above t = maybe False (== GT) . half t

-- | Determine whether /x/ lies below the halfway point between two representations.
-- 
-- @ 'below' t x '==' (x '-' 'unitl' t x) '`lt`' ('counitr' t x '-' x) @
--
below :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
below t = maybe False (== LT) . half t

-- | Determine whether /x/ lies exactly halfway between two representations.
-- 
-- @ 'tied' t x '==' (x '-' 'unitl' t x) '=~' ('counitr' t x '-' x) @
--
tied :: Prd a => Prd b => (Additive-Group) a => Trip a b -> a -> Bool
tied t = maybe False (== EQ) . half t

-- @ truncateWith C.id == id @
truncateWith :: (Prd a, Prd b, (Additive-Monoid) a) => Trip a b -> a -> b
truncateWith t x = bool (ceilingWith t x) (floorWith t x) $ x >= zero

-- @ ceilingWith C.id == id @
ceilingWith :: Prd a => Prd b => Trip a b -> a -> b
ceilingWith = connl . tripl

-- @ floorWith C.id == id @
floorWith :: Prd a => Prd b => Trip a b -> a -> b
floorWith = connr . tripr

-- @ roundWith C.id == id @
roundWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> a -> b
roundWith t x | above t x = ceilingWith t x -- upper half interval
              | below t x = floorWith t x -- lower half interval
              | otherwise = truncateWith t x

{-

rndWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b 
rndWith t@(Trip f g h) rm x = rnd t rm (neg' t rm x) (g x)

-}


-- >>> addWith ratf32 RTN 1 2
-- 3.0
-- minSubf
addWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> b 
addWith t@(Trip _ f _) rm x y = rnd t rm (addSgn t rm x y) (f x + f y)

negWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b 
negWith t@(Trip _ f _) rm x = rnd t rm (neg' t rm x) (zero - f x)

subWith :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> b 
subWith t@(Trip _ f _) rm x y = rnd t rm (subSgn t rm x y) (f x - f y)

mulWith :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b 
mulWith t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x * f y)

{-
big = shiftf (-1) maximal
λ> fmaWith ratf32 RTN big 2 (-big)
3.4028235e38
λ> big * 2 - big
Infinity
-}
fmaWith :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b -> b
fmaWith t@(Trip _ f _) rm x y z = rnd t rm (fmaSgn t rm x y z) $ f x * f y + f z

{-
λ> remWith @Int RTP 17 5
-3
λ> remWith @Int RNZ 17 5
2
-}
remWith :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b
remWith t rm x y = fmaWith t rm (negWith t rm $ divWith t rm x y) y x

{-
λ> divWith @Int RNZ 17 5
3
λ> divWith @Int RTP 17 5
4
-}
-- when pos numbers are divided by −0 we return minus infinity rather than pos:
-- >>> divWith C.id RNZ 1 (shiftf (-1) 0)
-- -Infinity
divWith :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b 
divWith t@(Trip _ f _) rm x y = rnd t rm (xorSgn t rm x y) (f x / f y)


-- requires that sign be flipped back in /a/.
divWith' :: (Prd a, Prd b, Field a) => Trip a b -> Mode -> b -> b -> b 
divWith' t@(Trip _ f _) rm x y | xorSgn t rm x y = rnd t rm True (negate $ f x / f y)
                               | otherwise  = rnd t rm False (f x / f y)


---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

-- Determine the sign of 0 when /a/ contains signed 0s
rsz :: (Prd a, Prd b) => Trip a b -> Bool -> a -> b
rsz t = bool (floorWith t) (ceilingWith t)

rnd :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> Bool -> a -> b
rnd t RNZ s x = bool (roundWith t x) (rsz t s x) $ x =~ zero
rnd t RTP s x = bool (ceilingWith t x) (rsz t s x) $ x =~ zero
rnd t RTN s x = bool (floorWith t x) (rsz t s x) $ x =~ zero
rnd t RTZ s x = bool (truncateWith t x) (rsz t s x) $ x =~ zero

neg' :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> Bool
neg' t rm x = x < rnd t rm False zero

pos'  :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> Bool 
pos' t rm x = x > rnd t rm False zero

-- | Determine signed-0 behavior under addition.
addSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
addSgn t rm x y | rm == RTN = neg' t rm x || neg' t rm y
                | otherwise = neg' t rm x && neg' t rm y

subSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
subSgn t rm x y = not (addSgn t rm x y)

-- | Determine signed-0 behavior under multiplication and division.
xorSgn :: (Prd a, Prd b, (Additive-Group) a) => Trip a b -> Mode -> b -> b -> Bool
xorSgn t rm x y = neg' t rm x `xor` neg' t rm y

fmaSgn :: (Prd a, Prd b, Ring a) => Trip a b -> Mode -> b -> b -> b -> Bool
fmaSgn t rm x y z = addSgn t rm (mulWith t rm x y) z
