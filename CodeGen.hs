-- CodeGen.hs CUDA pseudocode generator
--
-- Given the analysis result from ArrayAnalysis, generates CUDA-like
-- pseudocode showing the compilation strategy the compiler would choose.

module CodeGen
  ( generateCode
  , generateCodeAnnotated
  ) where

import MiniAcc
import ArrayAnalysis

generateCode :: AnalysisResult -> String
generateCode ar = case arShapeStability ar of
  ShapeStable -> generatePingPong ar
  ShapeVaries -> generateRealloc ar

generateCodeAnnotated :: AnalysisResult -> String
generateCodeAnnotated ar =
  let code = generateCode ar
      annot = generateAnnotations ar
  in annot ++ "\n" ++ code

-- Ping-pong strategy (shape-stable)
-- Allocate exactly 2 buffers of known size
-- Swap between them each iteration
-- Fuse the loop body into a single kernel if possible

generatePingPong :: AnalysisResult -> String
generatePingPong ar =
  let prog = arProgram ar
      sh   = wpInitShape prog
      dims = showDims sh
      bodyKernel = generateBodyKernel (arBodyFusion ar) (wpBody prog)
      condKernel = generateCondKernel (wpCondOps prog)
  in unlines
    [ "// === " ++ wpName prog ++ " ==="
    , "// Ping-pong buffers (shape stable)"
    , "//"
    , "// Allocate 2 buffers, no allocation inside the loop."
    , ""
    , "// --- Memory allocated once before the loop ---"
    , "size_t size = " ++ dims ++ " * sizeof(float);"
    , "float *buf_A, *buf_B;"
    , "cudaMalloc(&buf_A, size);    // buffer A"
    , "cudaMalloc(&buf_B, size);    // buffer B"
    , "cudaMemcpy(buf_A, initial_data, size, cudaMemcpyHostToDevice);"
    , ""
    , "// --- Iteration loop, no allocation or reallocation ---"
    , "bool converged = false;"
    , "while (!converged) {"
    , bodyKernel
    , ""
    , "    // Swap buffers (pointer swap, zero cost)"
    , "    float *tmp = buf_A; buf_A = buf_B; buf_B = tmp;"
    , ""
    , condKernel
    , "}"
    , ""
    , "// --- Cleanup ---"
    , "cudaMemcpy(result, buf_A, size, cudaMemcpyDeviceToHost);"
    , "cudaFree(buf_A);"
    , "cudaFree(buf_B);"
    , ""
    , "// Total cudaMalloc calls: 2"
    , "// Total cudaFree calls:   2"
    , "// Memory allocated per iteration: 0 bytes"
    ]



-- Not shape stable -> the compiler must conservatively reallocate
generateRealloc :: AnalysisResult -> String
generateRealloc ar =
  let prog = arProgram ar
      sh   = wpInitShape prog
      dims = showDims sh
      bodyKernel = generateBodyKernelRealloc (wpBody prog)
      condKernel = generateCondKernel (wpCondOps prog)
  in unlines
    [ "// === " ++ wpName prog ++ " ==="
    , "// Reallocate each iteration, not shape stable"
    , "//"
    , "// Analysis couldn't prove invariant"
    , "// Allocates new output buffer each iteration, then free the old one."
    , "// Of course this is much slower due to cudaMalloc inside the loop."
    , ""
    , "// --- Initial allocation ---"
    , "size_t current_size = " ++ dims ++ " * sizeof(float);"
    , "float *buf_current;"
    , "cudaMalloc(&buf_current, current_size);"
    , "cudaMemcpy(buf_current, initial_data, current_size, cudaMemcpyHostToDevice);"
    , ""
    , "// --- Iteration loop (ALLOCATES EVERY ITERATION) ---"
    , "bool converged = false;"
    , "int iteration = 0;"
    , "while (!converged) {"
    , "    // Must compute output size at runtime (data-dependent)"
    , "    size_t output_size = compute_output_size(buf_current, current_size);"
    , ""
    , "    // Allocate new buffer for this iteration's output"
    , "    float *buf_next;"
    , "    cudaMalloc(&buf_next, output_size); //expensive"
    , ""
    , bodyKernel
    , ""
    , "    // Free old buffer, advance"
    , "    cudaFree(buf_current);                 //expensive"
    , "    buf_current = buf_next;"
    , "    current_size = output_size;"
    , ""
    , condKernel
    , "    iteration++;"
    , "}"
    , ""
    , "// --- Cleanup ---"
    , "cudaMemcpy(result, buf_current, current_size, cudaMemcpyDeviceToHost);"
    , "cudaFree(buf_current);"
    , ""
    , "// Total cudaMalloc calls: 1 + N  (N = number of iterations)"
    , "// Total cudaFree calls:   1 + N"
    , "// Memory allocated per iteration: output_size bytes"
    , "// For 1000 iterations: ~10-50ms wasted on allocation alone!"
    ]


generateBodyKernel :: FusionInfo -> Pipeline -> String
generateBodyKernel fusion ops =
  case fusion of
    FullyFusable ->
      "    // Fused kernel: " ++ showOps ops ++ " → single kernel launch\n"
      ++ "    " ++ fusedKernelName ops ++ "<<<grid, block>>>(buf_A, buf_B);"
    PartiallyFusable ->
      "    // Partial fusion producers embedded into consumer\n"
      ++ "    " ++ fusedKernelName ops ++ "<<<grid, block>>>(buf_A, buf_B);"
    Unfusable ->
      unlines [ "    // Unfused " ++ show (length ops) ++ " separate kernel launches"
              | _ <- take 1 ops ]
      ++ unlines [ "    " ++ kernelName op ++ "<<<grid, block>>>(buf_A, buf_B);"
                 | op <- ops ]

generateBodyKernelRealloc :: Pipeline -> String
generateBodyKernelRealloc ops =
  unlines [ "    " ++ kernelName op ++ "<<<grid, block>>>(buf_current, buf_next);"
          | op <- ops ]

generateCondKernel :: Pipeline -> String
generateCondKernel ops =
  "    // Convergence check\n"
  ++ "    " ++ "convergence_kernel<<<grid, block>>>(buf_A, &converged);"

kernelName :: ArrayOp -> String
kernelName OpMap              = "map_kernel"
kernelName OpZipWith          = "zipwith_kernel"
kernelName OpFold             = "fold_kernel"
kernelName OpScan             = "scan_kernel"
kernelName OpStencil          = "stencil_kernel"
kernelName (OpGenerate _)     = "generate_kernel"
kernelName (OpBackpermute _)  = "backpermute_kernel"
kernelName OpFilter           = "filter_kernel"
kernelName OpSlice            = "slice_kernel"
kernelName (OpReplicate _)    = "replicate_kernel"

fusedKernelName :: Pipeline -> String
fusedKernelName ops = "fused_" ++ concatMap shortName ops ++ "_kernel"
  where
    shortName OpMap              = "map_"
    shortName OpZipWith          = "zip_"
    shortName OpFold             = "fold_"
    shortName OpScan             = "scan_"
    shortName OpStencil          = "stencil_"
    shortName (OpGenerate _)     = "gen_"
    shortName (OpBackpermute _)  = "bperm_"
    shortName OpFilter           = "filt_"
    shortName OpSlice            = "slice_"
    shortName (OpReplicate _)    = "rep_"

showOps :: Pipeline -> String
showOps ops = unwords (map showOp ops)
  where
    showOp OpMap              = "map"
    showOp OpZipWith          = "zipWith"
    showOp OpFold             = "fold"
    showOp OpScan             = "scan"
    showOp OpStencil          = "stencil"
    showOp (OpGenerate sh)    = "generate" ++ show sh
    showOp (OpBackpermute sh) = "backpermute" ++ show sh
    showOp OpFilter           = "filter"
    showOp OpSlice            = "slice"
    showOp (OpReplicate n)    = "replicate(" ++ show n ++ ")"

showDims :: [Int] -> String
showDims ds = foldr1 (\a b -> a ++ " * " ++ b) (map show ds)

generateAnnotations :: AnalysisResult -> String
generateAnnotations ar = unlines
  [ "╔══════════════════════════════════════════════════════════════════╗"
  , "║  Analysis: " ++ padRight 40 (wpName (arProgram ar)) ++ "║"
  , "╠══════════════════════════════════════════════════════════════════╣"
  , "║  Initial shape:     " ++ padRight 43 (show (wpInitShape (arProgram ar))) ++ "║"
  , "║  Loop body:         " ++ padRight 43 (showOps (wpBody (arProgram ar))) ++ "║"
  , "║  Shape stability:   " ++ padRight 43 (showStability (arShapeStability ar)) ++ "║"
  , "║  Loop invariant:    " ++ padRight 43 (showInvariantShape (arLoopInvariant ar)) ++ "║"
  , "║  Body fusion:       " ++ padRight 43 (show (arBodyFusion ar)) ++ "║"
  , "║  Fixpoint iters:    " ++ padRight 43 (show (arIterations ar)) ++ "║"
  , "║  Strategy:          " ++ padRight 43 (showStrategy (arShapeStability ar)) ++ "║"
  , "╚══════════════════════════════════════════════════════════════════╝"
  ]
  where
    showStability ShapeStable = "STABLE"
    showStability ShapeVaries = "VARIES"
    showInvariantShape desc = case adShape desc of
      ExactShape sh -> show sh ++ " (exact)"
      AnyShape      -> "? (data-dependent)"
    showStrategy ShapeStable = "PING-PONG (2 allocations total)"
    showStrategy ShapeVaries = "REALLOCATE (N+1 allocations)"

padRight :: Int -> String -> String
padRight n str = take n (str ++ repeat ' ')
