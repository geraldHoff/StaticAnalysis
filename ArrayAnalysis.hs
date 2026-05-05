-- ArrayAnalysis.hs — YAAM-derived analysis for array while-loops
--
-- Connection between AAM and MiniAcc array DSL. Implements abstract
-- transfer function for each array operation and uses YAAM's 
-- fixpoint to compute loop invariants.

module ArrayAnalysis
  (
    AnalysisResult(..)
  , ShapeStability(..)
  , analyzeWhile
  , analyzePipeline
  , analyzeWhileTrace
  ) where

import Fixpoint
import MiniAcc

data ShapeStability
  = ShapeStable
  | ShapeVaries
  deriving (Eq, Ord, Show)


data AnalysisResult = AnalysisResult
  { arProgram        :: WhileProgram
  , arShapeStability :: ShapeStability
  , arLoopInvariant  :: ArrayDesc
  , arInitialDesc    :: ArrayDesc
  , arBodyFusion     :: FusionInfo
  , arIterations     :: Int
  } deriving (Eq, Show)


transferOp :: ArrayDesc -> ArrayOp -> ArrayDesc

transferOp desc OpMap = desc
  { adProducer = IsMap
  , adFusion   = FullyFusable
  }

transferOp desc OpZipWith = desc
  { adProducer = IsZipWith
  , adFusion   = FullyFusable
  }

transferOp desc OpStencil = desc
  { adProducer = IsStencil
  , adFusion   = PartiallyFusable
  }

transferOp desc OpScan = desc
  { adProducer = IsConsumer
  , adFusion   = PartiallyFusable
  }

transferOp desc OpFold = desc
  { adShape    = foldShape (adShape desc)
  , adProducer = IsConsumer
  , adFusion   = PartiallyFusable
  }
  where
    foldShape (ExactShape ds)
      | length ds > 1 = ExactShape (init ds)
      | otherwise     = ExactShape []
    foldShape AnyShape = AnyShape

transferOp desc (OpGenerate sh) = desc
  { adShape    = ExactShape sh
  , adProducer = IsGenerate
  , adFusion   = FullyFusable
  }

transferOp desc (OpBackpermute sh) = desc
  { adShape    = ExactShape sh
  , adProducer = IsBackpermute
  , adFusion   = FullyFusable
  }

transferOp desc OpFilter = desc
  { adShape    = AnyShape
  , adProducer = IsUnknown
  , adFusion   = Unfusable
  }

transferOp desc OpSlice = desc
  { adShape    = sliceShape (adShape desc)
  , adProducer = IsBackpermute
  , adFusion   = FullyFusable
  }
  where
    sliceShape (ExactShape ds)
      | length ds > 1 = ExactShape (init ds)
      | otherwise     = ExactShape []
    sliceShape AnyShape = AnyShape

transferOp desc (OpReplicate n) = desc
  { adShape    = repShape (adShape desc)
  , adProducer = IsBackpermute
  , adFusion   = FullyFusable
  }
  where
    repShape (ExactShape ds) = ExactShape (ds ++ [n])
    repShape AnyShape        = AnyShape


--function composition over the abstract domain.

-- straight-line pipeline
analyzePipeline :: ArrayDesc -> Pipeline -> ArrayDesc
analyzePipeline = foldl transferOp

-- fusability
classifyFusion :: Pipeline -> FusionInfo
classifyFusion ops
  | all isProducerOp ops                      = FullyFusable
  | all isProducerOp (init ops) && isConsumerOp (last ops)
                                               = PartiallyFusable
  | otherwise                                  = Unfusable
  where
    isProducerOp OpMap           = True
    isProducerOp OpZipWith       = True
    isProducerOp (OpGenerate _)  = True
    isProducerOp (OpBackpermute _) = True
    isProducerOp _               = False
    isConsumerOp OpFold           = True
    isConsumerOp OpScan           = True
    isConsumerOp OpStencil        = True
    isConsumerOp _                = False



-- Analyze a while-loop program
analyzeWhile :: WhileProgram -> AnalysisResult
analyzeWhile prog =
  let
      initDesc = ArrayDesc
        { adShape    = ExactShape (wpInitShape prog)
        , adProducer = IsManifest
        , adFusion   = Unfusable
        }

      bodyTransfer :: ArrayDesc -> ArrayDesc
      bodyTransfer desc = analyzePipeline desc (wpBody prog)

      widenStep :: ArrayDesc -> ArrayDesc
      widenStep current =
        let next = bodyTransfer current
        in current ⊔ next

      -- Run AAM fixpoint algorithm
      (loopInvariant, iters) = fixpointN widenStep initDesc

      -- Determine shape stability from the invariant
      stability = case adShape loopInvariant of
        ExactShape sh
          | sh == wpInitShape prog -> ShapeStable
          | otherwise              -> ShapeVaries
        AnyShape -> ShapeVaries

      bodyFusion = classifyFusion (wpBody prog)

  in AnalysisResult
      { arProgram        = prog
      , arShapeStability = stability
      , arLoopInvariant  = loopInvariant
      , arInitialDesc    = initDesc
      , arBodyFusion     = bodyFusion
      , arIterations     = iters
      }

-- Analyze trace with intermediate array descriptors
-- Shows how the fixpoint converges.
analyzeWhileTrace :: WhileProgram -> (AnalysisResult, [ArrayDesc])
analyzeWhileTrace prog =
  let initDesc = ArrayDesc
        { adShape    = ExactShape (wpInitShape prog)
        , adProducer = IsManifest
        , adFusion   = Unfusable
        }

      bodyTransfer desc = analyzePipeline desc (wpBody prog)

      widenStep current =
        let next = bodyTransfer current
        in current ⊔ next

      trace = fixpointTrace widenStep initDesc

  in (analyzeWhile prog, trace)
