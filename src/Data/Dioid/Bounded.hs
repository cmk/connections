{-# Language ConstraintKinds #-}
{-# Language Rank2Types #-}

module Numeric.Signed where

import Data.Prd.Infix
import Data.Connection
import Data.Semiring
import Numeric.IEEE.Float

import Prelude hiding (Float, Ord(..))



-- | 'Sign' is isomorphic to 'Maybe Ordering' and (Bool,Bool), but has a distinct poset ordering:
--
-- @ 'Indeterminate' >= 'Positive' >= 'Zero'@ and
-- @ 'Indeterminate' >= 'Negative' >= 'Zero'@ 
--
-- Note that 'Positive' and 'Negative' are not comparable. 
--
--   * 'Positive' can be regarded as representing (0, +∞], 
--   * 'Negative' as representing [−∞, 0), 
--   * 'Indeterminate' as representing [−∞, +∞] v NaN, and 
--   * 'Zero' as representing the set {0}.
--
data Sign = Zero | Negative | Positive | Indeterminate deriving (Show, Eq)

sign' :: (Num a, Prd a) => a -> Sign
sign' x = case sign x of
    Nothing -> Indeterminate
    Just EQ -> Zero
    Just LT -> Negative
    Just GT -> Positive

instance Semigroup Sign where

    Positive <> Positive            = Positive
    Positive <> Negative            = Indeterminate
    Positive <> Zero                = Positive
    Positive <> Indeterminate       = Indeterminate

    Negative <> Positive            = Indeterminate
    Negative <> Negative            = Negative
    Negative <> Zero                = Negative
    Negative <> Indeterminate       = Indeterminate

    Zero <> a                       = a

    Indeterminate <> _              = Indeterminate


instance Monoid Sign where

    mempty = Zero


instance Semiring Sign where

    Positive >< a = a

    Negative >< Positive            = Negative
    Negative >< Negative            = Positive
    Negative >< Zero                = Zero
    Negative >< Indeterminate       = Indeterminate

    Zero >< _                       = Zero

    --NB: measure theoretic zero
    Indeterminate >< Zero           = Zero
    Indeterminate >< _              = Indeterminate

    fromBoolean = fromBooleanDef Positive

instance Bounded Sign where
    minBound = Zero
    maxBound = Indeterminate

-- TODO if we dont use canonical ordering then we can define a
-- monotone map to floats
instance Prd Sign where
    Positive `le` Positive         = True
    Positive `le` Negative         = False
    Positive `le` Zero             = False
    Positive `le` Indeterminate    = True 

    Negative `le` Positive         = False
    Negative `le` Negative         = True
    Negative `le` Zero             = False
    Negative `le` Indeterminate    = True
    
    --Zero `le` Indeterminate        = False
    Zero `le` _                    = True

    Indeterminate `le` Indeterminate  = True
    Indeterminate `le` _              = False


newtype Signed = Signed Float

instance Show Signed where
    show (Signed x) = show x

instance Prd Signed where
    -- neither connex nor semiconnex
    pcompare (Signed x) (Signed y) = pcompare (split y) (split x)


float_signed :: Trip Float Signed
float_signed = Trip f g h where
  f x = if signBit x then Signed $ proj x else Signed x

  g (Signed x) = x

  h x = if signBit x then Signed x else Signed $ proj x

  proj x = if nan x then x else 
               (if signBit x then -0 else 0)



--plus_minus :: Signed -> Conn Signed Signed
--plus_minus x = Conn (x<>) (x\\) 

-- x // y = max {z: z <> y <= x}
-- x \\ y = max {z: x <> z <= y}

signBit' = not . signBit

instance Semigroup Signed where
    Signed x <> Signed y = Signed $ x + y



{-
(\\) :: Unsigned -> Unsigned -> Unsigned
Unsigned x \\ Unsigned y = Unsigned $ y - x

(\\) :: Signed -> Signed -> Signed
Signed x \\ Signed y = Signed $ y - x

 | signBit x && signBit y = Signed $ if y - x <= (-0) then y - x else -0
                     | signBit' x && signBit' y = Signed $ if y - x <= 0 then y - x else 0
-}

newtype Unsigned = Unsigned Float

unsigned :: Signed -> Unsigned
unsigned (Signed x) = Unsigned (abs x)

instance Show Unsigned where
    show (Unsigned x) = show $ abs x

-- Unsigned has a interval semiorder containing all joins.
instance Prd Unsigned where
    u `lt` v = ltun u v

    -- @ pInf * 0 ~~ NaN ~~ 0 @
    -- makes for a lower-complete lattice with distributive & annihilative multiplication
    u@(Unsigned x) `eq` v@(Unsigned y) | zero x && nan y = True
                                       | zero y && nan x = True
                                       | otherwise = not (u `lt` v) && not (v `lt` u)
    u@(Unsigned x) `le` v@(Unsigned y) = u `lt` v || (abs x) `eqn` (abs y) 


ltun (Unsigned x) (Unsigned y) | pos (abs x) && nan y = False
                               | pos (abs y) && nan x = True
                               | finite x && finite y = shift 2 (abs x) `lt` (abs y)
                               | finite x && infinite y = True
                               | otherwise = False
eqn :: Float -> Float -> Bool
eqn x y = within 2 x y || zero x && nan y || zero y && nan x || nan y && nan x

abs'' x | nan x = 0
       | otherwise = abs x
instance Semigroup Unsigned where
    Unsigned x <> Unsigned y = Unsigned $ abs'' x + abs'' y

instance Monoid Unsigned where
    mempty = Unsigned 0

instance Semiring Unsigned where
    Unsigned x >< Unsigned y = Unsigned $ abs x * abs y
    fromBoolean = fromBooleanDef (Unsigned 1)
{-

instance Lattice (Signed a) where
  (Signed x) \/ (Signed y) | both pos = Signed $ min (abs x) (abs y)

  (Signed x) \/ (Signed y) | mixed signs = Signed $ min (abs x) (abs y)

instance Semilattice (Unsigned a) where
  (Unsigned x) \/ (Unsigned y) | nan y = x--bias to first nan
  (Unsigned x) \/ (Unsigned y) | nan x = y
  (Unsigned x) \/ (Unsigned y) = fmin x y

signedSign :: Trip Signed Sign

floatPositive :: Trip Float Signed
floatPositive

-}
