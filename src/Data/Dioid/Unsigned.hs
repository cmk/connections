{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
module Data.Dioid.Unsigned where

import Control.Category ((>>>))
import Data.Bifunctor (first)
import Data.Connection hiding (first)
import Data.Connection.Float
import Data.Float
import Data.Dioid.Signed
import Data.Prd
import Data.Prd.Nan
import Prelude

--import Language.Haskell.TH.Syntax (Q, Exp(..), lift, liftData, dataToExpQ)
--import Language.Haskell.TH.Quote (QuasiQuoter (..))

sgnugn :: Conn Signed (Nan Unsigned)
sgnugn = Conn f g where
  f (Signed x) = Unsigned <$> liftNan (max 0) x 
  g (Def (Unsigned x)) = Signed $ if isNanf x then pInf else abs x
  g Nan = Signed (0/0)

-- @ 'f32ugn' == 'f32sgn' '>>>' 'sgnugn' @
--
f32ugn :: Conn Float (Nan Unsigned)
f32ugn = Conn f g where
  f x = Unsigned <$> liftNan (max 0) x
  g (Def (Unsigned x)) = if isNanf x then pInf else abs x
  g Nan = 0/0

--TODO 
--export qquoter rather than constructor

newtype Unsigned = Unsigned Float

unsigned :: Float -> Unsigned
unsigned x = Unsigned (abs x)

fromUnsigned :: Unsigned -> Float
fromUnsigned (Unsigned x) = x

instance Show Unsigned where
    show (Unsigned x) = show x

instance Eq Unsigned where
    (Unsigned x) == (Unsigned y) | finite x && finite y = (abs x) == (abs y) 
                                 | not (finite x) && not (finite y) = True  --NaNs are equiv to Inf
                                 | otherwise = False

-- Unsigned has a 2-Ulp interval semiorder containing all joins and meets.
instance Prd Unsigned where
    -- corresponds when float has a 2-ulp semiorder and nans are handled
    u <~ v = u `ltugn` v || u == v 

ltugn :: Unsigned -> Unsigned -> Bool
ltugn (Unsigned x) (Unsigned y) 
  | finite x && finite y = (abs x) < shift (-2) (abs y) 
  | finite x && not (finite y) = True
  | otherwise = False

{-
ltun (Unsigned x) (Unsigned y) | finite x && indeterminate y = True
                               | finite y && indeterminate x = False
                               | finite x && finite y = shift 1 (abs x) `lt` (abs y)
                               | finite x && infinite y = True
                               | otherwise = False

ltun (Unsigned x) (Unsigned y) | positive (abs x) && indeterminate y = True
                               | positive (abs y) && indeterminate x = False
                               | finite x && finite y = shift 2 (abs x) `lt` (abs y)
                               | finite x && infinite y = True
                               | otherwise = False

eqn :: Float -> Float -> Bool
eqn x y = within 2 x y || zero x && indeterminate y || zero y && indeterminate x || indeterminate y && indeterminate x

-}
instance Minimal Unsigned where
    minimal = Unsigned 0

instance Maximal Unsigned where
    maximal = Unsigned pInf

joinugn (Unsigned x) (Unsigned y) | finite x && finite y = Unsigned $ max (abs x) (abs y)
                                  | finite x && not (finite y) = Unsigned y
                                  | otherwise = Unsigned x

meetugn (Unsigned x) (Unsigned y) | finite x && finite y = Unsigned $ min (abs x) (abs y)
                                  | not (finite x) && finite y = Unsigned y
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
    --x <> y <~ z iff y <~ x \\ z iff x <~ z // y.
    Unsigned y // Unsigned x | y == x = Unsigned 0
           | otherwise = Unsigned $ let z = y - x in if z + x <~ y then sup (x+) z y else inf'' (x+) z y
-}

{-

    residr :: a -> Conn a a
    residr x = Conn (x<>) (x\\)

    residl :: a -> Conn a a
    residl x = Conn (<>x) (//x)

foo :: (Index b, Num b) => b -> b -> b
foo x y = let z = y - x in if z + x <~ y then sup (x+) z y else inf'' (x+) z y

--instance Min Unsigned where minimal = Unsigned 0



sgnugn :: Trip Signed (Nan (Either Unsigned Unsigned))


instance Lattice (Signed a) where
  (Signed x) \/ (Signed y) | both positive = Signed $ min (abs x) (abs y)

  (Signed x) \/ (Signed y) | mixed signs = Signed $ min (abs x) (abs y)

instance Semilattice (Unsigned a) where
  (Unsigned x) \/ (Unsigned y) | indeterminate y = x--bias to first indeterminate
  (Unsigned x) \/ (Unsigned y) | indeterminate x = y
  (Unsigned x) \/ (Unsigned y) = fmin x y


-}
{-
--TODO make Positive/Unsigned semiring instances ('qualitative' Dioids (incl nan, pinf,ninf)) on *,+?
-- are there conditions under which the ops are associative?

-- | Newtype representing a non-negateative real number. 
--
-- Morally equivalent to 'Maybe Positive'.
newtype Unsigned a = Unsigned { unUnsigned :: a }
  deriving (Eq, Ord, Show, Generic)


instance Num a => Semigroup (Unsigned a) where
  Unsigned a <> Unsigned b  = Unsigned $ a + b

instance Num a => Monoid (Unsigned a) where
  mempty = Unsigned 0

instance Num a => Semiring (Unsigned a) where
  Unsigned a >< Unsigned b  = Unsigned $ a * b
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Unsigned 1

instance (Ord a, Num a) => Dioid (Unsigned a) where
  Unsigned a <~ Unsigned b = a <= b


unsigned :: (Ord a, Num a) => a -> Maybe (Unsigned a)
unsigned = bool Nothing <$> Just . Unsigned <*> (0 <=)


-- | A quasiquoter for safely constructing a 'Unsigned Float' from a constant.
--
-- >>> [nnf|1.0|]
-- Unsigned {unUnsigned = 1.0}
nnf :: QuasiQuoter
nnf = let
    msg = "Invalid non-negateative (must be >= 0)"
    mk s = readMaybe @Float s >>= unsigned
    in qq $ justErr msg . mk


-- | A quasiquoter for safely constructing a 'Unsigned Double' from a constant.
--
-- >>> [nnd|1.0|]
-- Unsigned {unUnsigned = 1.0}
nnd :: QuasiQuoter
nnd = let
    msg = "Invalid non-negateative (must be >= 0)"
    mk s = readMaybe @Double s >>= unsigned
    in qq $ justErr msg . mk

-- ----------------------------------------------------------------------------

-- | Newtype representing a strictly positive number.
newtype Positive a = Positive { unPositive :: a } 
  deriving (Eq, Ord, Show, Data, Generic)

{-
instance Num a => Semigroup (Positive a) where
  Positive a <> Positive b  = Positive $ a + b


instance Num a => Semiring (Positive a) where
  Positive a >< Positive b  = Positive $ a * b
  {-# INLINE (><) #-}


instance (Ord a, Num a) => Dioid (Positive a) where
  Positive a <~ Positive b = a <= b
-}

positive :: (Ord a, Num a) => a -> Maybe (Positive a)
positive = bool Nothing <$> Just . Positive <*> (0 <)


-- | A quasiquoter for safely constructing a 'Positive Float' from a constant.
--
-- >>> [pf|1.0|]
-- Positive {unPositive = 1.0}
pf :: QuasiQuoter
pf = let
    msg = "Invalid positive (must be > 0)"
    mk s = readMaybe @Float s >>= positive
    in qq $ justErr msg . mk


-- | A quasiquoter for safely constructing a 'Positive Double' from a constant.
--
-- >>> [pd|1.0|]
-- Positive {unPositive = 1.0}
pd :: QuasiQuoter
pd = let
    msg = "Invalid positive (must be >= 0)"
    mk s = readMaybe @Double s >>= positive
    in qq $ justErr msg . mk


-- | A quasiquoter for safely constructing a 'Positive Natural' from a constant.
--
-- >>> [pn|1.0|]
-- Positive {unPositive = 1.0}
pn :: QuasiQuoter
pn = let
    msg = "Invalid positive (must be >= 0)"
    mk s = readMaybe @Natural s >>= positive
    in qq $ justErr msg . mk

-------------------------------------------------------------------------------
-- 'Unit'
-------------------------------------------------------------------------------

-- | The unit interval dioid.
newtype Unit a = Unit { unUnit :: a }
  deriving (Eq, Ord, Show, Data, Generic, GenUnchecked, GenValid, Typeable, Validity)


instance Num a => Bounded (Unit a) where
  minBound = Unit 0
  maxBound = Unit 1


instance Ord a => Semigroup (Unit a) where
  Unit a <> Unit b  = Unit $ max a b


instance (Ord a, Num a) => Monoid (Unit a) where
  mempty = Unit 0


instance (Ord a, Num a) => Semiring (Unit a) where
  Unit a >< Unit b  = Unit $ a * b
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Unit 1


instance (Ord a, Num a) => Dioid (Unit a) where
  Unit a <~ Unit b = a <= b


instance (Ord a, Num a) => Closed (Unit a) where
  star _ = one
  plus = id


inRange :: Ord a => a -> a -> a -> Bool
inRange low high = (&&) <$> (low <=) <*> (<= high)

unit :: (Ord a, Num a) => a -> Maybe (Unit a)
unit = bool Nothing <$> (Just . Unit) <*> inRange 0 1


-- | A quasiquoter for safely constructing a 'Unit Float' from a constant.
--
-- >>> [uf|1.0|]
-- Unit {unUnit = 1.0}
uf :: QuasiQuoter
uf = let
    msg = "Invalid unit (must be in [0,1])"
    mk s = readMaybe @Float s >>= unit
    in qq $ justErr msg . mk


-- | A quasiquoter for safely constructing a 'Unit Double' from a constant.
--
-- >>> [ud|1.0|]
-- Unit {unUnit = 1.0}
ud :: QuasiQuoter
ud = let
    msg = "Invalid unit (must be in [0,1])"
    mk s = readMaybe @Double s >>= unit
    in qq $ justErr msg . mk


-- | Safe `Unit` complement
complement :: Num a => Unit a -> Unit a
complement (Unit a) = Unit $ 1 - a


-- | Safe `Unit` division
--div' :: Unit a -> Positive a -> Unit a
--div' (Unit n) (Positive d) = Unit $ n / d

-------------------------------------------------------------------------------
-- Internal
-------------------------------------------------------------------------------

qq :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qq = qqLift liftData

-- Necessary when `Text` is involved, https://stackoverflow.com/q/38143464
qqText :: Data a => ([Char] -> Either [Char] a) -> QuasiQuoter
qqText = qqLift liftDataWithText
  where
    liftText :: T.Text -> Q Exp
    liftText = fmap (AppE $ VarE 'T.pack) . lift . T.unpack

    liftDataWithText :: Data a => a -> Q Exp
    liftDataWithText = dataToExpQ (fmap liftText . cast)

qqLift :: (a -> Q Exp) -> ([Char] -> Either [Char] a) -> QuasiQuoter
qqLift l f = QuasiQuoter {
    quoteExp = either fail l . f
  , quotePat = no "patterns"
  , quoteType = no "types"
  , quoteDec = no "declarations"
  }
  where no c = const (fail ("This QQ produces expressions, not " <> c))
-}
