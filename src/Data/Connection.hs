{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Safe #-}
{-# OPTIONS_HADDOCK show-extensions #-}

-- |
--
-- This library provides connections between common types, combinators & accessors,
-- including lawful versions of 'floor', 'ceiling', 'round', and 'truncate'. There
-- is also a separately exported 'Data.Connection.Class.Connection' class. Lastly,
-- there are 'Data.Lattice.Semilattice' and 'Data.Lattice.Algebra' classes
-- based on the same construction.
--
-- /connections/ is extensively tested, and it exports properties for use in testing
-- your own connections. See "Data.Connection.Property" and "Data.Lattice.Property".
-- In addition to the property tests there are several doctests scattered around,
-- these are runnable as a standalone executable. See the /doctest/ stanza in the
-- library's cabal file.
module Data.Connection (
   
    -- $example
    
    Side(..),
    
    -- * Types

    -- ** CastL
    castL,
    pattern CastL,
    
    -- ** CastR
    castR,
    pattern CastR,
    
    -- ** Cast
    cast,
    pattern Cast,
    Cast,
    
    -- * Accessors
    midpoint,
    interval,
    
    -- ** upper
    upper,
    upper1,
    upper2,
    
    -- ** lower
    lower,
    lower1,
    lower2,
    
    -- ** ceiling
    ceiling,
    ceiling1,
    ceiling2,
   
    -- ** floor
    floor,
    floor1,
    floor2,
   
    -- ** round
    round,
    round1,
    round2,
    
    -- ** truncate
    truncate,
    truncate1,
    truncate2,
    
    -- ** max/min
    maximize,
    minimize,
    median,

    -- * Combinators
    (>>>),
    (<<<),
    swapL,
    swapR,
    mapped,
    choice,
    select,
    strong,
    divide,
    
    -- * Extended
    extended,
    Extended (..),

) where

import safe Data.Connection.Cast
import safe Data.Connection.Class
import safe Prelude hiding (ceiling, floor, round, truncate)

{- $example
 
 ==== What is a Galois connection?

 A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection) is an 
 adjunction in the category of preorders: a pair of monotone maps /f :: p -> q/
 and /g :: q -> p/ between preorders /p/ and /q/, such that

 /f x <= y/ if and only if /x <= g y/

 We say that /f/ is the left or lower adjoint, and /g/ is the right or upper
 adjoint of the connection.

 For illustration, here is a simple example from
 [7 Sketches](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf):

 <<img/example.png example>>

 Note that the two component functions are each monotonic:

 @ x1 'Data.Order.Syntax.<=' x2 implies f x1 'Data.Order.Syntax.<=' f x2 @

 and furthermore they are are interlocked (i.e. adjoint) in the specific way
 outlined above:

 @ f x 'Data.Order.Syntax.<=' y if and only if x 'Data.Order.Syntax.<=' g y @

 See the [README](https://github.com/cmk/connections/blob/master/README.md) for
 a more extensive overview.
-}
