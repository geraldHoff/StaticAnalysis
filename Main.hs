-- Main.hs --- AAM-Accelerate Demonstration
--
-- Demonstrates that AAM-derived abstract interpretation, applied to
-- an Accelerate-like array DSL with while-loops, produces analysis
-- results that enable the GPU compiler to choose between efficient
-- ping-pong buffer management and conservative reallocation.
--
-- unghc Main.hs

module Main where

import MiniAcc
import ArrayAnalysis
import CodeGen


main :: IO ()
main = do
  putStrLn banner

  let programs = [jacobi, mandelbrot, fixedGenerate, iterativeFilter, kmeans]

  putStrLn ""
  putStrLn "Loop invariant analysis"
  putStrLn ""

  let results = map analyzeWhile programs
  mapM_ printAnalysis (zip programs results)

  putStrLn ""
  putStrLn "Compilation"
  putStrLn ""

  let jacobiResult = results !! 0
      filterResult = results !! 3

  putStrLn (generateCodeAnnotated jacobiResult)
  putStrLn (generateCode jacobiResult)

  putStrLn (replicate 70 '─')
  putStrLn ""

  putStrLn (generateCodeAnnotated filterResult)
  putStrLn (generateCode filterResult)

  putStrLn ""
  putStrLn "Fixpoint convergence traces"
  putStrLn ""

  -- Show how the fixpoint converges for each program
  mapM_ printTrace programs

printAnalysis :: (WhileProgram, AnalysisResult) -> IO ()
printAnalysis (prog, result) = do
  putStrLn $ "┌── " ++ wpName prog ++ " ---"
  putStrLn $ "│"
  putStrLn $ "│  " ++ head (lines (wpDesc prog))
  mapM_ (\l -> putStrLn $ "│  " ++ l) (tail (lines (wpDesc prog)))
  putStrLn $ "│"
  putStrLn $ "│  Analysis result:"
  putStrLn $ "│    Shape stability:  " ++ showStab (arShapeStability result)
  putStrLn $ "│    Loop invariant:   " ++ showShape (adShape (arLoopInvariant result))
  putStrLn $ "│    Producer class:   " ++ show (adProducer (arLoopInvariant result))
  putStrLn $ "│    Body fusability:  " ++ show (arBodyFusion result)
  putStrLn $ "│    Fixpoint iters:   " ++ show (arIterations result)
  putStrLn $ "│    Compile strategy: " ++ showStrat (arShapeStability result)
  putStrLn $ "└──"
  putStrLn ""

printTrace :: WhileProgram -> IO ()
printTrace prog = do
  let (_, trace) = analyzeWhileTrace prog
  putStrLn $ "--- " ++ wpName prog ++ " ---"
  putStrLn $ "   Fixpoint convergence trace:"
  mapM_ (\(i, desc) ->
    putStrLn $ "     iteration " ++ show i ++ ": shape = "
            ++ showShape (adShape desc)
            ++ ", producer = " ++ show (adProducer desc)
    ) (zip [0..] trace)
  putStrLn $ "     fixpoint reached after " ++ show (length trace - 1)
          ++ " iteration(s)"
  putStrLn ""

showStab :: ShapeStability -> String
showStab ShapeStable = "STABLE"
showStab ShapeVaries = "VARIES"

showShape :: AbsShape -> String
showShape (ExactShape sh) = show sh
showShape AnyShape        = "? (unknown)"

showStrat :: ShapeStability -> String
showStrat ShapeStable = "ping-pong buffers (optimal)"
showStrat ShapeVaries = "reallocate each iteration (conservative)"

banner :: String
banner = unlines
  [ ""
  , "╔══════════════════════════════════════════════════════════════════╗"
  , "║     AAM × Accelerate: Abstract Analysis for GPU Loops         ║"
  , "╚══════════════════════════════════════════════════════════════════╝"
  , ""
  ]