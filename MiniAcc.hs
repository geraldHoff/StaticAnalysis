-- Minimal Accelerate-like DSL
--
-- A tiny embedded language representing GPU array programs
-- `Awhile` combinator for iterative computations.

module MiniAcc
  (
    ArrayOp(..)
  , Pipeline
  , WhileProgram(..)
  , TopLevel(..)
  , AbsShape(..)
  , ProducerClass(..)
  , ArrayDesc(..)
  , FusionInfo(..)
  , jacobi
  , iterativeFilter
  , kmeans
  , mandelbrot
  , fixedGenerate
  ) where

import Fixpoint (Lattice(..))


data ArrayOp
  = OpMap              -- map f arr: preserves shape, element-wise
  | OpZipWith          -- zipWith f a b: preserves shape
  | OpFold             -- fold f z arr: removes innermost dimension
  | OpScan             -- scanl/scanr: preserves shape
  | OpStencil          -- stencil s boundary arr: preserves shape
  | OpGenerate [Int]   -- generate sh f: produces array with given shape
  | OpBackpermute [Int]-- backpermute sh p arr: changes to specified shape
  | OpFilter           -- filter: output size depends on data (not shape!)
  | OpSlice            -- slice: removes one dimension
  | OpReplicate Int    -- replicate: adds one dimension of given size
  deriving (Eq, Ord, Show)

type Pipeline = [ArrayOp]


data WhileProgram = WhileProgram
  { wpName       :: String
  , wpInitShape  :: [Int]
  , wpBody       :: Pipeline
  , wpCondOps    :: Pipeline
  , wpDesc       :: String
  } deriving (Eq, Show)

data TopLevel
  = TWhile WhileProgram
  | TPipeline String [Int] Pipeline
  deriving (Eq, Show)

data AbsShape
  = ExactShape [Int]  -- known dimensions, e.g. [1024, 1024]
  | AnyShape
  deriving (Eq, Ord, Show)

-- Classification of array producers for fusion decisions.
data ProducerClass
  = IsMap
  | IsZipWith
  | IsStencil
  | IsGenerate
  | IsBackpermute
  | IsManifest
  | IsFused [ProducerClass]
  | IsConsumer
  | IsUnknown
  deriving (Eq, Ord, Show)

data FusionInfo
  = FullyFusable
  | PartiallyFusable
  | Unfusable
  deriving (Eq, Ord, Show)

data ArrayDesc = ArrayDesc
  { adShape    :: AbsShape
  , adProducer :: ProducerClass
  , adFusion   :: FusionInfo
  } deriving (Eq, Ord, Show)

-- Lattice instance for the abstract domain
-- The ordering determines when the fixpoint iteration terminates:
--   ExactShape [n,m] ⊑ ExactShape [n,m]   (equal)
--   ExactShape [n,m] ⊑ AnyShape           (less precise)
--   AnyShape ⊑ AnyShape                   (equal)
-- Join (⊔) computes the least upper bound:
--   ExactShape [n,m] ⊔ ExactShape [n,m] = ExactShape [n,m]
--   ExactShape [n,m] ⊔ ExactShape [p,q] = AnyShape  (different shapes!)
--   anything ⊔ AnyShape = AnyShape

instance Lattice AbsShape where
  bot = ExactShape []
  top = AnyShape
  ExactShape a ⊑ ExactShape b = a == b
  ExactShape _ ⊑ AnyShape     = True
  AnyShape   ⊑ ExactShape _   = False
  AnyShape   ⊑ AnyShape       = True
  ExactShape a ⊔ ExactShape b
    | a == b    = ExactShape a
    | otherwise = AnyShape
  _ ⊔ _ = AnyShape
  ExactShape a ⊓ ExactShape b
    | a == b    = ExactShape a
    | otherwise = bot
  AnyShape ⊓ x = x
  x ⊓ AnyShape = x

instance Lattice ArrayDesc where
  bot = ArrayDesc (ExactShape []) IsUnknown Unfusable
  top = ArrayDesc AnyShape IsUnknown Unfusable
  a ⊑ b = adShape a ⊑ adShape b
  a ⊔ b = ArrayDesc
    { adShape    = adShape a ⊔ adShape b
    , adProducer = mergeProducer (adProducer a) (adProducer b)
    , adFusion   = mergeFusion (adFusion a) (adFusion b)
    }
  a ⊓ b = ArrayDesc
    { adShape    = adShape a ⊓ adShape b
    , adProducer = adProducer a
    , adFusion   = adFusion a
    }

mergeProducer :: ProducerClass -> ProducerClass -> ProducerClass
mergeProducer a b | a == b = a
mergeProducer _ _ = IsUnknown

mergeFusion :: FusionInfo -> FusionInfo -> FusionInfo
mergeFusion FullyFusable FullyFusable = FullyFusable
mergeFusion PartiallyFusable PartiallyFusable = PartiallyFusable
mergeFusion _ _ = Unfusable

-- Examples

-- | Jacobi relaxation for Laplace's equation.
--   Body: stencil averaging with 4 neighbours.
--   Condition: fold(max(abs(zipWith(-) old new))) > epsilon
--   Shape: PRESERVED across all iterations.
jacobi :: WhileProgram
jacobi = WhileProgram
  { wpName      = "Jacobi Relaxation (Laplace)"
  , wpInitShape = [1024, 1024]
  , wpBody      = [ OpStencil ]          -- one stencil convolution per iteration
  , wpCondOps   = [ OpZipWith            -- diff = zipWith (-) old new
                  , OpMap                 -- abs(diff)
                  , OpFold               -- max reduction
                  ]
  , wpDesc      = "Solve ∇²u = 0 by iterative stencil averaging.\n"
              ++ "  Body: stencil (4-point Laplacian)\n"
              ++ "  Condition: max |u_new - u_old| > ε\n"
              ++ "  Expected: shape [1024,1024] stable across iterations"
  }

-- | Iterative filter: repeatedly remove elements below threshold.
--   Body: filter elements.
--   Shape: CHANGES every iteration (data-dependent).
iterativeFilter :: WhileProgram
iterativeFilter = WhileProgram
  { wpName      = "Iterative Filter"
  , wpInitShape = [10000]
  , wpBody      = [ OpFilter ]           -- filter shrinks the array
  , wpCondOps   = [ OpFold ]             -- check if any elements remain
  , wpDesc      = "Repeatedly filter elements below threshold.\n"
              ++ "  Body: filter (data-dependent size)\n"
              ++ "  Condition: length(arr) > 0\n"
              ++ "  Expected: shape becomes unknown (data-dependent)"
  }

-- | K-means clustering: reassign points then recompute centroids.
--   Body: backpermute (regroup points) then fold (average per cluster).
--   The fold changes shape, but in a structured way.
kmeans :: WhileProgram
kmeans = WhileProgram
  { wpName      = "K-Means Clustering"
  , wpInitShape = [100, 2]    -- 100 points, 2D
  , wpBody      = [ OpBackpermute [100, 2]  -- regroup points by nearest centroid
                  , OpFold                   -- reduce to k centroids (shape changes!)
                  ]
  , wpCondOps   = [ OpZipWith, OpMap, OpFold ]  -- max centroid displacement > epsilon
  , wpDesc      = "K-means: reassign points to clusters, recompute centroids.\n"
              ++ "  Body: backpermute (regroup) then fold (average)\n"
              ++ "  Condition: max centroid displacement > ε\n"
              ++ "  Expected: fold changes shape → not trivially stable"
  }

-- | Mandelbrot iteration with fixed bounds.
--   Body: zipWith + map (compute z² + c, check escape).
--   Shape: PRESERVED (grid dimensions fixed).
mandelbrot :: WhileProgram
mandelbrot = WhileProgram
  { wpName      = "Mandelbrot Iteration"
  , wpInitShape = [2048, 2048]
  , wpBody      = [ OpZipWith    -- z² + c (complex arithmetic)
                  , OpMap        -- check |z| < 2
                  ]
  , wpCondOps   = [ OpFold ]    -- any pixel still iterating?
  , wpDesc      = "Mandelbrot set: z_{n+1} = z_n² + c with escape check.\n"
              ++ "  Body: zipWith (z²+c), map (escape test)\n"
              ++ "  Condition: any pixel not escaped\n"
              ++ "  Expected: shape [2048,2048] stable"
  }

-- | Fixed-shape generation: generate then map.
--   Shape always determined by the generate.
fixedGenerate :: WhileProgram
fixedGenerate = WhileProgram
  { wpName      = "Fixed Generate + Map"
  , wpInitShape = [512, 512]
  , wpBody      = [ OpGenerate [512, 512], OpMap ]
  , wpCondOps   = [ OpFold ]
  , wpDesc      = "Regenerate array from indices each iteration.\n"
              ++ "  Body: generate [512,512], map\n"
              ++ "  Condition: convergence check\n"
              ++ "  Expected: shape [512,512] stable (forced by generate)"
  }
