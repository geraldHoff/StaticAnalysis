-- Core abstract interpretation engine based on:
--   "Systematic Abstraction of Abstract Machines"
--   David Van Horn and Matthew Might (2011)
--
-- This module provides the general fixpoint machinery, lattice
-- infrastructure, and store-widened analysis algorithm. Domain-specific
-- analyses (e.g. array shape analysis for GPU compilation) instantiate
-- these abstractions with their own value domains.

module Fixpoint
  ( -- * Lattice class
    Lattice(..)
    -- * Fixpoint computation
  , fixpoint
  , fixpointN
  , fixpointTrace
  ) where

-- An abstract domain forms a lattice: values can be joined (⊔) to
-- produce sound over-approximations, and the partial order (⊑)
-- determines when the analysis has stabilized.

class Eq a => Lattice a where
  bot  :: a           -- least element
  top  :: a           -- greatest element
  (⊑)  :: a -> a -> Bool  -- partial order
  (⊔)  :: a -> a -> a     -- least upper bound (join)
  (⊓)  :: a -> a -> a     -- greatest lower bound (meet)

-- Fixpoint computation
-- iterate a monotonic function over a lattice
-- until the result stabilizes. Store-bounding guarantees the lattice
-- has finite height, so this always terminates.
-- | Compute the least fixpoint of a monotonic function.
--   Terminates when f(x) = x.
fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x =
  let x' = f x
  in if x' == x then x else fixpoint f x'

fixpointN :: Eq a => (a -> a) -> a -> (a, Int)
fixpointN f = go 0
  where
    go n x =
      let x' = f x
      in if x' == x then (x, n) else go (n + 1) x'

fixpointTrace :: Eq a => (a -> a) -> a -> [a]
fixpointTrace f = go
  where
    go x =
      let x' = f x
      in x : if x' == x then [] else go x'
