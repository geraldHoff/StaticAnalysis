-- AAM.hs
-- Abstracting Abstract Machines: Abstract time-stamped CESK* with expression-string time
--
-- Based on: "Systematic Abstraction of Abstract Machines"
--           David Van Horn and Matthew Might
--           Journal of Functional Programming, 22(4-5), September 2012.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Prelude hiding ((!!))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Utility type synonyms and operators

-- Finite map synonym (paper uses :->)
type k :-> v = Map.Map k v

-- Powerset synonym (paper uses P)
type P s = Set.Set s

-- Functional extension: f // [x ==> y]
(==>) :: a -> b -> (a, b)
x ==> y = (x, y)

(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
f // [(x, y)] = Map.insert x y f

-- Partial map lookup
(!) :: (Ord k, Show k) => (k :-> v) -> k -> v
f ! key = case Map.lookup key f of
  Just v  -> v
  Nothing -> error $ "lookup failed"

-- Lattice infrastructure

class Lattice a where
  bot :: a
  top :: a
  (⊑) :: a -> a -> Bool
  (⊔) :: a -> a -> a
  (⊓) :: a -> a -> a

-- Sets ordered by inclusion form a lattice
instance (Ord s) => Lattice (P s) where
  bot   = Set.empty
  top   = error "no representation of universal set"
  x ⊔ y = Set.union x y
  x ⊓ y = Set.intersection x y
  x ⊑ y = Set.isSubsetOf x y

-- Maps lifted pointwise into lattices
instance (Ord k, Lattice v) => Lattice (k :-> v) where
  bot   = Map.empty
  top   = error "no representation of top map"
  f ⊑ g = Map.isSubmapOfBy (⊑) f g
  f ⊔ g = Map.unionWith (⊔) f g
  f ⊓ g = Map.intersectionWith (⊓) f g

-- Lookup with default bottom for abstract stores
(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! key = Map.findWithDefault bot key f

-- Join a single entry into an abstract store
(⊔!) :: (Ord k, Lattice v) => (k :-> v) -> [(k, v)] -> (k :-> v)
f ⊔! [(key, v)] = Map.insertWith (⊔) key v f

-- Singleton set shorthand
s :: (Ord a) => a -> P a
s = Set.singleton

-- Syntax

type Var = String

data Lambda = Var :=> Exp
  deriving (Eq, Ord, Show)

data Exp
  = Ref Var         -- variable reference
  | Lam Lambda      -- lambda abstraction
  | Exp :@ Exp      -- application
  deriving (Eq, Ord, Show)

-- Semantic domains (abstract, k-CFA-like with expression-string time)

-- Abstract machine state
type Sigma = (Exp, Env, Store, Kont, Time)

-- Storable values: closures or continuations
data Storable
  = Clo (Lambda, Env)
  | Cont Kont
  deriving (Eq, Ord, Show)

-- Environments map variables to addresses
type Env = Var :-> Addr

-- Abstract store maps addresses to *sets* of storable values
type Store = Addr :-> P Storable

-- Continuations with store-allocated predecessor (address, not recursive)
data Kont
  = Mt
  | Ar (Exp, Env, Addr)
  | Fn (Lambda, Env, Addr)
  deriving (Eq, Ord, Show)

-- Time is a bounded list of expressions (contour / call string)
type Time = [Exp]

-- Addresses: either for bindings or for continuations
data Addr
  = BAddr (Var, Time)     -- binding address
  | KAddr (Exp, Time)     -- continuation address
  deriving (Eq, Ord, Show)

-- Parameters: k, tick, alloc

-- The k parameter controls context-sensitivity.
-- k = 0 gives 0-CFA-like monovariance.
-- k = 1 gives 1-CFA-like analysis.
k :: Int
k = 1

-- Advance time by prepending current expression, truncating to k.
tick :: Sigma -> Time
tick (e, _, _, _, t) = take k (e : t)

-- Allocate a binding address from a variable and the current time.
allocBind :: Var -> Time -> Addr
allocBind v t = BAddr (v, t)

-- Allocate a continuation address from an expression and the current time.
allocKont :: Exp -> Time -> Addr
allocKont e t = KAddr (e, t)

-- Abstract transition relation (nondeterministic)

step :: Sigma -> [Sigma]

-- Variable reference: look up variable in store, nondeterministically
-- choose among the set of values at that address.
step state@(Ref x, rho, sigma, kappa, t) =
  [ (Lam lam, rho', sigma, kappa, t')
  | Clo (lam, rho') <- Set.toList (sigma !! (rho ! x))
  ]
  where t' = tick state

-- Application: evaluate operator, push argument continuation.
step state@(f :@ e, rho, sigma, kappa, t) =
  [ (f, rho, sigma', kappa', t') ]
  where
    t'     = tick state
    a'     = allocKont (f :@ e) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]
    kappa' = Ar (e, rho, a')

-- Operator evaluated, now evaluate argument.
step state@(Lam lam, rho, sigma, Ar (e, rho', a'), t) =
  [ (e, rho', sigma, Fn (lam, rho, a'), t') ]
  where t' = tick state

-- Argument evaluated, perform application: bind parameter, restore continuation.
step state@(Lam lam, rho, sigma, Fn (x :=> e, rho', a), t) =
  [ ( e
    , rho' // [x ==> a']
    , sigma ⊔! [a' ==> s (Clo (lam, rho))]
    , kappa
    , t'
    )
  | Cont kappa <- Set.toList (sigma !! a)
  ]
  where
    t' = tick state
    a' = allocBind x t'

-- Final state: value with empty continuation, no transitions.
step (Lam _, _, _, Mt, _) = []

-- Catch-all for unexpected states.
step st = error $ "stuck state: " ++ show st

-- Injection: program -> initial abstract state

inject :: Exp -> Sigma
inject e = (e, Map.empty, Map.empty, Mt, [])

-- State-space exploration, graph search

-- Compute reachable abstract states from a program.
aval :: Exp -> P Sigma
aval e = explore step (inject e)

-- Explore reachable state-space of a nondeterministic transition system.
explore :: (Ord a) => (a -> [a]) -> a -> P a
explore f s0 = search f Set.empty [s0]

-- Worklist-based graph search.
search :: (Ord a) => (a -> [a]) -> P a -> [a] -> P a
search _ seen [] = seen
search f seen (hd : tl)
  | hd `Set.member` seen = search f seen tl
  | otherwise             = search f (Set.insert hd seen) (f hd ++ tl)

-- Analysis

-- Check if a state is a final (value with empty continuation).
isFinal :: Sigma -> Bool
isFinal (Lam _, _, _, Mt, _) = True
isFinal _                    = False

-- Extract final states from the analysis result.
finalStates :: P Sigma -> P Sigma
finalStates = Set.filter isFinal

-- Extract all lambdas that appear as values in final states.
finalValues :: P Sigma -> P Lambda
finalValues states = Set.fromList
  [ lam | (Lam lam, _, _, Mt, _) <- Set.toList states ]

-- Tests

-- Identity: (λx.x)
ident :: Exp
ident = Lam ("x" :=> Ref "x")

-- Church numeral zero: (λf.λx.x)
zero :: Exp
zero = Lam ("f" :=> Lam ("x" :=> Ref "x"))

-- Church successor: (λn.λf.λx. f (n f x))
succE :: Exp
succE = Lam ("n" :=> Lam ("f" :=> Lam ("x" :=>
  (Ref "f" :@ (Ref "n" :@ Ref "f" :@ Ref "x")))))

-- Self-application: (λx. x x)
omega1 :: Exp
omega1 = Lam ("x" :=> (Ref "x" :@ Ref "x"))

-- Omega (non-terminating): (λx. x x)(λx. x x)
omega :: Exp
omega = omega1 :@ omega1

-- Simple application: (λx.x)(λy.y)
test1 :: Exp
test1 = ident :@ Lam ("y" :=> Ref "y")

-- Two-argument function: (λf. f (λx.x)) (λg. g (λy.y))
test2 :: Exp
test2 = Lam ("f" :=> (Ref "f" :@ Lam ("x" :=> Ref "x")))
     :@ Lam ("g" :=> (Ref "g" :@ Lam ("y" :=> Ref "y")))

-- Church one applied: (succ zero)
test3 :: Exp
test3 = succE :@ zero

showExp :: Exp -> String
showExp (Ref x)    = x
showExp (Lam (x :=> e)) = "(λ" ++ x ++ "." ++ showExp e ++ ")"
showExp (f :@ e)   = "(" ++ showExp f ++ " " ++ showExp e ++ ")"

showResults :: P Sigma -> String
showResults states =
  let n     = Set.size states
      fins  = finalStates states
      nFin  = Set.size fins
      vals  = finalValues states
  in unlines
    [ "Reachable states: " ++ show n
    , "Final states:     " ++ show nFin
    , "Result values:    " ++ show (Set.size vals)
    , "Values:"
    ] ++ unlines [ "  " ++ show lam | lam <- Set.toList vals ]

main :: IO ()
main = do
  let tests = [ ("(λx.x)(λy.y)",       test1)
              , ("((λf.f(λx.x))(λg.g(λy.y)))", test2)
              , ("succ zero",           test3)
              ]

  mapM_ (\(name, prog) -> do
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "Program: " ++ showExp prog
    let result = aval prog
    putStrLn $ showResults result
    ) tests

  -- Omega should be reachable but not have a final state
  putStrLn "=== omega (non-terminating) ==="
  putStrLn $ "Program: " ++ showExp omega
  let omegaResult = aval omega
  putStrLn $ showResults omegaResult
