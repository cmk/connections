{-# Language ConstraintKinds #-}

module Data.Float.Signed where

import Control.Applicative
import Control.Category ((>>>))
import Data.Bifunctor (first)
import Data.Connection hiding (first)
import Data.Connection.Float
import Data.Float
import Data.Semifield
import Data.Prd
import Data.Prd.Nan
--import Data.Dioid
--import Data.Semigroup.Quantale
import Data.Semigroup.Additive
import Data.Semigroup.Multiplicative
import Data.Semigroup.Join
import Data.Semigroup.Meet
import Data.Semiring
import Prelude hiding (Ord(..), Num(..), Fractional(..))

--import Language.Haskell.TH.Syntax (Q, Exp(..), lift, liftData, dataToExpQ)
--import Language.Haskell.TH.Quote (QuasiQuoter (..))


sgnugn :: Conn Signed (Nan Unsigned)
sgnugn = Conn f g where
  f (Signed x) = Unsigned <$> liftNan (max 0) x 
  g (Def (Unsigned x)) = Signed $ if isNan x then pinf else abs x
  g Nan = Signed (0/0)

-- @ 'f32ugn' == 'f32sgn' '>>>' 'sgnugn' @
--
f64ugn :: Conn Double (Nan Unsigned)
f64ugn = Conn f g where
  f x = Unsigned <$> liftNan (max 0) x
  g (Def (Unsigned x)) = if isNan x then pinf else abs x
  g Nan = 0/0

--TODO 
--export qquoter rather than constructor

newtype Unsigned = Unsigned Double

unsigned :: Double -> Unsigned
unsigned x = Unsigned (abs x)

fromUnsigned :: Unsigned -> Double
fromUnsigned (Unsigned x) = x

instance Show Unsigned where
    show (Unsigned x) = show x

instance Eq Unsigned where
    (Unsigned x) == (Unsigned y) | fin' x && fin' y = (abs x) == (abs y) 
                                 | not (fin' x) && not (fin' y) = True  --NaNs are equiv to Inf
                                 | otherwise = False

-- Unsigned has a 2-Ulp interval semiorder containing all joins and meets.
instance Prd Unsigned where
    -- corresponds when float has a 2-ulp semiorder and nans are handled
    u <= v = u `ltugn` v || u == v 

ltugn :: Unsigned -> Unsigned -> Bool
ltugn (Unsigned x) (Unsigned y) 
  | fin' x && fin' y = (abs x) < shift (-2) (abs y) 
  | fin' x && not (fin' y) = True
  | otherwise = False

{-
ltun (Unsigned x) (Unsigned y) | fin' x && ind y = True
                               | fin' y && ind x = False
                               | fin' x && fin' y = shiftf 1 (abs x) `lt` (abs y)
                               | fin' x && infin' y = True
                               | otherwise = False

ltun (Unsigned x) (Unsigned y) | pos (abs x) && ind y = True
                               | pos (abs y) && ind x = False
                               | fin' x && fin' y = shiftf 2 (abs x) `lt` (abs y)
                               | fin' x && infin' y = True
                               | otherwise = False

eqn :: Double -> Double -> Bool
eqn x y = within 2 x y || zero x && ind y || zero y && ind x || ind y && ind x

-}
instance Minimal Unsigned where
    minimal = Unsigned zero

instance Maximal Unsigned where
    maximal = Unsigned pinf

joinUgn (Unsigned x) (Unsigned y) | fin' x && fin' y = Unsigned $ max (abs x) (abs y)
                                  | fin' x && not (fin' y) = Unsigned y
                                  | otherwise = Unsigned x

meetUgn (Unsigned x) (Unsigned y) | fin' x && fin' y = Unsigned $ min (abs x) (abs y)
                                  | not (fin' x) && fin' y = Unsigned y
                                  | otherwise = Unsigned x
{-

instance Semigroup Unsigned where
    Unsigned x <> Unsigned y = Unsigned $ abs x + abs y

instance Monoid (Additive Unsigned) where
    mempty = Additive $ Unsigned 0

instance Monoid (Multiplicative Unsigned) where
    mempty = Multiplicative $ Unsigned 1

instance Semiring Unsigned where
    Unsigned x >< Unsigned y | zero x || zero y = Unsigned 0
                             | otherwise = Unsigned $ abs x * abs y
    fromBoolean = fromBooleanDef (Unsigned 1)

instance Quantale Unsigned where
    x \\ y = y // x

    Unsigned y // Unsigned x = Unsigned . max 0 $ y // x
-}

{-
    --x <> y <= z iff y <= x \\ z iff x <= z // y.
    Unsigned y // Unsigned x | y == x = Unsigned 0
           | otherwise = Unsigned $ let z = y - x in if z + x <= y then sup (x+) z y else inf'' (x+) z y
-}

{-

    residr :: a -> Conn a a
    residr x = Conn (x<>) (x\\)

    residl :: a -> Conn a a
    residl x = Conn (<>x) (//x)

foo :: (Index b, Num b) => b -> b -> b
foo x y = let z = y - x in if z + x <= y then sup (x+) z y else inf'' (x+) z y

--instance Min Unsigned where minimal = Unsigned 0



sgnugn :: Trip Signed (Nan (Either Unsigned Unsigned))


instance Lattice (Signed a) where
  (Signed x) \/ (Signed y) | both pos = Signed $ min (abs x) (abs y)

  (Signed x) \/ (Signed y) | mixed signs = Signed $ min (abs x) (abs y)

instance Semilattice (Unsigned a) where
  (Unsigned x) \/ (Unsigned y) | ind y = x--bias to first ind
  (Unsigned x) \/ (Unsigned y) | ind x = y
  (Unsigned x) \/ (Unsigned y) = fmin x y


-}


-- | 
--
-- Signed is a floating point value with a magnitude-based partial order
-- within each sign, but the traditional order between signs.
--
newtype Signed = Signed { unSigned :: Double } deriving Show


-- Trip (Signed a) (Inf (Nan Ordering))
-- Conn Signed (Nan (Either (Down Unsigned) Unsigned))


f64sgn :: Conn Double Signed
f64sgn = Conn f g where
  f x | x == ninf = Signed $ -0
      | otherwise = Signed $ either (const 0) id $ split x

  g (Signed x) = either (const ninf) id $ split x

instance Eq Signed where
  (==) = (=~)

{-
instance (Semiring a, Prd a) => Eq (Signed a) where
    (Signed x) == (Signed y) | ind x && ind y = True 
                             | ind x || ind y = False
                             | otherwise = x =~ y -- 0 /= -0

s = Signed anan :: Signed Double
p = Signed pinf :: Signed Double
n = Signed ninf :: Signed Double
x = Signed 4.3
y = Signed (-4.3)

λ> s =~ s
True
λ> n <= p
True
λ> n <= s
True
λ> s <= p
True
λ> s <= (Signed 4)
False
λ> s ~~ (Signed 4)
True
-}

instance Prd Signed where
  pcompare (Signed x) (Signed y) | x /= x && y /= y = Just EQ 
                                 | x /= x || y /= y = Nothing 
                                 | otherwise = pcompare (first Down $ split x) (first Down $ split y)

{-
 | x /= x && y /= y = True 
           | x /= x || y /= y = False
           | otherwise        = x <= y

    pcompare (Signed x) (Signed y) | ind x && ind y = Just EQ 
                                   | ind x || ind y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)

type FieldLaw a = ((Additive-Group) a, (Multiplicative-Group) a)
-}


{-
joinSigned :: (Semifield a, Prd a) => Signed a -> Signed a -> Signed a
joinSigned (Signed a) (Signed b) = Signed $ maybe pinf id $ pmax a b

meetSigned :: Field a => Prd a => a -> a -> a 
meetSigned a b = maybe ninf id $ pmin a b

instance Field a => Semigroup (Join (Signed a)) where
  (<>) = liftA2 joinSigned

instance Field a => Monoid (Join (Signed a)) where
  mempty = Join (Signed ninf)

-- Signed
-- Signed is a floating point value with a magnitude-based partial order
-- within each sign, but the traditional order between signs.

-- Conn Signed (Nan (Either (Down Unsigned) Unsigned))

newtype Signed = Signed { unSigned :: Double }

f32spl :: Conn Double Signed
f32spl = Conn f g where
  f x | x == ninf = Signed $ -0
      | otherwise = Signed $ either (const 0) id $ split x

  g (Signed x) = either (const ninf) id $ split x


instance Show Signed where
    show (Signed x) = show x

instance Eq Signed where
    (Signed x) == (Signed y) | ind x && ind y = True 
                             | ind x || ind y = False
                             | otherwise = split x == split y -- 0 /= -0

instance Prd Signed where
    Signed x <= Signed y | ind x && ind y = True
                         | ind x || ind y = False
                         | otherwise = (first Down $ split x) <= (first Down $ split y)

    pcompare (Signed x) (Signed y) | ind x && ind y = Just EQ 
                                   | ind x || ind y = Nothing 
                                   | otherwise = pcompare (first Down $ split x) (first Down $ split y)


-- Canonical ordering semigroup
-- >>> Signed (-1) + Signed 3
-- 3.0
-- >>> Signed (-1) + Signed (-3)
-- -4.0
-- >>> Signed 1 + Signed 3
-- 4.0
instance Semigroup (Additive Signed) where
    (<>) = liftA2 $ \(Signed a) (Signed b) -> Signed . either id id $ split a + split b

instance Semigroup (Multiplicative Signed) where
    (<>) = liftA2 $ \(Signed a) (Signed b) -> Signed . either id id $ split a * split b

-- λ>  Signed (-1) * Signed (-3) --TODO is this a lawful presemiring?
-- 3.0
instance Presemiring Signed


instance Index Signed where
    type Idx Signed = Nan (Either Word64 Word64)

tripr af32sgn >>> idx @Double

(tripr af32sgn >>> idx)
  :: Conn Signed (Data.Prd.NanPrd.Nan GHC.Word.Word64)
-}

