# AAM x Accelerate

**Prototype demonstration that AAM-derived abstract interpretation enables efficient
compilation of iterative GPU programs.**

## Project

A prototype showing that the technique from Van Horn & Might's "Systematic
Abstraction of Abstract Machines" (2011), instantiated with an abstract domain
of array descriptors, can analyze while-loops over GPU arrays and produce
information sufficient for the compiler to choose between efficient and
conservative memory management strategies.

## Previous Limitations

[Accelerate](https://github.com/AccelerateHS/accelerate) is a Haskell EDSL
for GPU programming. It disallows recursion because its skeleton-based code
generator needs to know the complete structure of a computation at compile
time. This forces users to manually orchestrate iterative algorithms (Jacobi
relaxation, k-means, conjugate gradient) through host-side Haskell loops,
shuttling data across the CPU-GPU bus each iteration.

Accelerate has the GPU compilation machinery (skeleton-based code
generation, producer/consumer fusion, CUDA template instantiation) but bans
recursion because it cannot analyze loops.

AMM has the fixpoint analysis framework (store-bounding, abstract
GC, soundness theorem, termination guarantee) but knows nothing about arrays,
GPU memory, kernel fusion, or SIMD compilation.

AAM and Accelerate combined and extended allow for thie fixpoint algorithm,
instantiated with the abstract domain of array descriptors, computes exactly
the information Accelerate's compiler needs to handle `awhile`. One analysis
framework, applied uniformly to any loop pattern, with guaranteed termination
and soundness.

## Contribution

Add an `awhile` combinator to Accelerate and use a AAM-derived analysis to
compute loop invariants that tell the compiler what it needs to know:

- **Shape stability**: does the array shape change across iterations?
  If not → allocate two buffers once, ping-pong between them.
  If so → conservatively reallocate each iteration.

- **Fusability**: can the loop body be compiled as a single fused kernel?

- **Memory lifetime**: which intermediate arrays die between iterations?

The analysis terminates because the abstract domain has finite height (the
lattice of array descriptors is bounded), and YAAM's fixpoint iteration is
monotonic over this lattice.

## Files

```
aam-accelerate/

Fixpoints.hs              Core fixpoint/lattice infrastructure.
                         General-purpose; domain-independent.

AAM.hs              AAM applied to a lambda calculus with
                         conditionals, mutation, while loops, and
                         abstract GC. Standalone demonstration that
                         the technique works on a general language.

MiniAcc.hs            Mini Accelerate DSL. Defines array operations,
                         the Awhile construct, the abstract array domain
                         (AbsShape, ProducerClass, ArrayDesc), and
                         example programs (Jacobi, filter, k-means, etc).

ArrayAnalysis.hs      AAM-based analysis of MiniAcc while-loops.
                         Implements abstract transfer functions for each
                         array operation and uses AAM's fixpoint to
                         compute loop invariants.

CodeGen.hs            CUDA pseudocode generator. Emits different code
                         depending on analysis results: ping-pong for
                         shape-stable loops, reallocation for varying.

Main.hs               Entry point. Anaeslyz all example programs.
```

### Run demo with:

```bash
runghc Main.hs
```

or compile:

```bash
ghc --make Main.hs -o yaam-demo && ./yaam-demo
```

### Lambda calculus machine (standalone)

```bash
runghc AAM.hs
```

## Output

Analyzes 5 programs with the same framework:
- Jacobi, Mandelbrot, Fixed Generate → stable shape
- Iterative Filter, K-Means → shape varies

Shows the contrasting generated code:
- Jacobi gets ping-pong buffers (2 `cudaMalloc` calls total)
- Filter gets per-iteration reallocation (N+1 `cudaMalloc` calls)

Fixpoint convergence traces:
- Shape-preserving loops converge in 0 iterations (identity fixpoint)
- Shape-changing loops converge in 1 iteration (to `AnyShape`)

## References

- Van Horn & Might, "Systematic Abstraction of Abstract Machines", JFP 2011
- McDonell et al., "Optimising Purely Functional GPU Programs", ICFP 2013
