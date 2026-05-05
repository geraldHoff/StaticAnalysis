-- AAM.hs
-- Abstracting Abstract Machines: Extended with conditionals, mutation,
-- while loops, numeric/boolean literals, abstract GC, and store-widened
-- fixpoint analysis.
--
-- Based on: "Systematic Abstraction of Abstract Machines"
--           David Van Horn and Matthew Might (2011)
--           Sections 1-5 (CESK*, conditionals, mutation, GC)
--
-- Research extension: while combinator for Accelerate-style fixpoint loops.

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Prelude hiding ((!!))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (intercalate)

-- Utility type synonyms and operators

type k :-> v = Map.Map k v
type P s = Set.Set s

(==>) :: a -> b -> (a, b)
x ==> y = (x, y)

(//) :: Ord a => (a :-> b) -> [(a, b)] -> (a :-> b)
f // [(x, y)] = Map.insert x y f

(!) :: (Ord k, Show k) => (k :-> v) -> k -> v
f ! key = case Map.lookup key f of
  Just v  -> v
  Nothing -> error $ "lookup failed for key: " ++ show key

-- Lattice

class Lattice a where
  bot :: a
  top :: a
  (⊑) :: a -> a -> Bool
  (⊔) :: a -> a -> a
  (⊓) :: a -> a -> a

instance (Ord s) => Lattice (P s) where
  bot   = Set.empty
  top   = error "no representation of universal set"
  x ⊔ y = Set.union x y
  x ⊓ y = Set.intersection x y
  x ⊑ y = Set.isSubsetOf x y

instance (Ord k, Lattice v) => Lattice (k :-> v) where
  bot   = Map.empty
  top   = error "no representation of top map"
  f ⊑ g = Map.isSubmapOfBy (⊑) f g
  f ⊔ g = Map.unionWith (⊔) f g
  f ⊓ g = Map.intersectionWith (⊓) f g

(!!) :: (Ord k, Lattice v) => (k :-> v) -> k -> v
f !! key = Map.findWithDefault bot key f

(⊔!) :: (Ord k, Lattice v) => (k :-> v) -> [(k, v)] -> (k :-> v)
f ⊔! [] = f
f ⊔! ((key, v) : rest) = (Map.insertWith (⊔) key v f) ⊔! rest

s :: (Ord a) => a -> P a
s = Set.singleton

-- Syntax (extended with conditionals, set!, while, literals)
--
-- e ∈ Exp ::= x | (e e) | (λx.e) | (if e e e) | (set! x e)
--           | (while e e) | #t | #f | n | (prim e e)

type Var = String

data Lambda = Var :=> Exp
  deriving (Eq, Ord, Show)

data PrimOp = Add | Sub | Mul | Eq | Lt | Gt
  deriving (Eq, Ord, Show)

data Lit = LBool Bool | LInt Int | AnyInt
  deriving (Eq, Ord, Show)

data Exp
  = Ref Var              -- variable reference
  | Lam Lambda           -- lambda abstraction
  | Exp :@ Exp           -- application
  | If Exp Exp Exp       -- conditional
  | Set Var Exp          -- mutation: (set! x e)
  | While Exp Exp        -- while loop: (while cond body)
  | Lit Lit              -- literal: boolean or integer
  | Prim PrimOp Exp Exp  -- primitive binary operation
  deriving (Eq, Ord, Show)

-- Free variables (needed for abstract GC)
fv :: Exp -> Set.Set Var
fv (Ref x)         = Set.singleton x
fv (Lam (x :=> e)) = Set.delete x (fv e)
fv (f :@ e)        = fv f `Set.union` fv e
fv (If c t el)     = fv c `Set.union` fv t `Set.union` fv el
fv (Set x e)       = Set.insert x (fv e)
fv (While c b)     = fv c `Set.union` fv b
fv (Lit _)         = Set.empty
fv (Prim _ e1 e2)  = fv e1 `Set.union` fv e2


-- Semantic domains
-- Addresses: binding or continuation
data Addr
  = BAddr (Var, Time)
  | KAddr (Exp, Time)
  deriving (Eq, Ord, Show)

-- Time is a bounded list of expressions (contour / call string)
type Time = [Exp]

-- Environments map variables to addresses
type Env = Var :-> Addr

-- Abstract store maps addresses to *sets* of storable values
type Store = Addr :-> P Storable

-- Storable values
data Storable
  = Clo (Lambda, Env)   -- closure
  | Cont Kont           -- continuation
  | LitVal Lit          -- literal value
  deriving (Eq, Ord, Show)

-- Continuations with store-allocated predecessor
data Kont
  = Mt
  | Ar (Exp, Env, Addr)
  | Fn (Lambda, Env, Addr)
  | IfK (Exp, Exp, Env, Addr)
  | SetK (Var, Addr, Addr)
  | WhileCondK (Exp, Exp, Env, Addr)
  | WhileBodyK (Exp, Exp, Env, Addr)
  | PrimLeftK (PrimOp, Exp, Env, Addr)
  | PrimRightK (PrimOp, Storable, Addr)
  deriving (Eq, Ord, Show)

-- Full machine state
type Sigma = (Exp, Env, Store, Kont, Time)

-- Partial state (for store-widened analysis)
type PartialState = (Exp, Env, Kont, Time)

-- The analysis system: set of partial states + global store
type System = (P PartialState, Store)


-- Parameters: k, tick, alloc

kParam :: Int
kParam = 0  -- 0-CFA for polynomial complexity with store widening

tick :: Sigma -> Time
tick (e, _, _, _, t) = take kParam (e : t)

allocBind :: Var -> Time -> Addr
allocBind v t = BAddr (v, t)

allocKont :: Exp -> Time -> Addr
allocKont e t = KAddr (e, t)

-- Checking value types

-- Is a storable value "falsy"? (only #f is false, following Scheme convention)
isFalsy :: Storable -> Bool
isFalsy (LitVal (LBool False)) = True
isFalsy _                      = False

-- Is a storable a value (not a continuation)?
isValue :: Storable -> Bool
isValue (Cont _) = False
isValue _        = True


-- Abstract transition relation (nondeterministic, store-widened)
--
-- Each step takes a (PartialState, Store) and returns a list of
-- (PartialState, Store) pairs. The store is threaded through but
-- the fixpoint algorithm joins stores globally.

step :: (PartialState, Store) -> [(PartialState, Store)]

-- Variable reference: look up in store, nondeterministically choose a value
step ((Ref x, rho, kappa, t), sigma) =
  [ case val of
      Clo (lam, rho') -> ((Lam lam, rho', kappa, t'), sigma)
      LitVal lit      -> ((Lit lit, Map.empty, kappa, t'), sigma)
      _               -> error "non-value in variable lookup"
  | val <- Set.toList (sigma !! (rho ! x))
  , isValue val
  ]
  where t' = take kParam (Ref x : t)

-- Application: evaluate operator, push argument continuation
step ((f :@ e, rho, kappa, t), sigma) =
  [ ((f, rho, Ar (e, rho, a'), t'), sigma') ]
  where
    t'     = take kParam (f :@ e : t)
    a'     = allocKont (f :@ e) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]

-- Operator is a lambda, evaluate argument
step ((Lam lam, rho, Ar (e, rho', a'), t), sigma) =
  [ ((e, rho', Fn (lam, rho, a'), t'), sigma) ]
  where t' = take kParam (Lam lam : t)

-- Argument evaluated (lambda), apply function
step ((Lam lam, rho, Fn (x :=> e, rho', a), t), sigma) =
  [ ((e, rho' // [x ==> a'], kappa, t'), sigma')
  | Cont kappa <- Set.toList (sigma !! a)
  ]
  where
    t'     = take kParam (Lam lam : t)
    a'     = allocBind x t'
    sigma' = sigma ⊔! [a' ==> s (Clo (lam, rho))]

-- Argument evaluated (literal), apply function
step ((Lit lit, _, Fn (x :=> e, rho', a), t), sigma) =
  [ ((e, rho' // [x ==> a'], kappa, t'), sigma')
  | Cont kappa <- Set.toList (sigma !! a)
  ]
  where
    t'     = take kParam (Lit lit : t)
    a'     = allocBind x t'
    sigma' = sigma ⊔! [a' ==> s (LitVal lit)]

-- Conditionals (Section 4.1)

-- (if e0 e1 e2): evaluate condition, push IfK continuation
step ((If e0 e1 e2, rho, kappa, t), sigma) =
  [ ((e0, rho, IfK (e1, e2, rho, a'), t'), sigma') ]
  where
    t'     = take kParam (If e0 e1 e2 : t)
    a'     = allocKont (If e0 e1 e2) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]

-- Condition evaluated to #f: take else branch
-- Condition evaluated to non-#f: take then branch
-- In the abstract, both branches may be reachable!
step ((Lam lam, rho, IfK (e1, e2, rho', a), t), sigma) =
  -- non-false: take then branch
  [ ((e1, rho', kappa, t'), sigma)
  | Cont kappa <- Set.toList (sigma !! a)
  ] ++
  -- also explore else branch if this could be false (it can't for Lam, but
  -- for soundness in the abstract, we could. However, a Lam is never #f.)
  []
  where t' = take kParam (Lam lam : t)

-- For a concrete literal, we know precisely whether it's truthy or falsy.
-- Abstraction imprecision arises from variable lookups (multiple values at
-- one address), not from known literal values.
step ((Lit lit, _, IfK (e1, e2, rho', a), t), sigma) =
  (if isFalsy (LitVal lit)
    then []  -- definitely false: skip then-branch
    else [ ((e1, rho', kappa, t'), sigma) | Cont kappa <- Set.toList (sigma !! a) ]
  ) ++
  (if isFalsy (LitVal lit)
    then [ ((e2, rho', kappa, t'), sigma) | Cont kappa <- Set.toList (sigma !! a) ]
    else []  -- definitely true: skip else-branch
  )
  where t' = take kParam (Lit lit : t)

-- Mutation: (set! x e) (Section 4.1)

-- (set! x e): evaluate e, push SetK continuation
step ((Set x e, rho, kappa, t), sigma) =
  [ ((e, rho, SetK (x, rho ! x, a'), t'), sigma') ]
  where
    t'     = take kParam (Set x e : t)
    a'     = allocKont (Set x e) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]

-- Value returned to SetK: update store, return previous value
step ((Lam lam, rho, SetK (x, varAddr, a), t), sigma) =
  [ ((Lam lam, rho, kappa, t'), sigma')
  | Cont kappa <- Set.toList (sigma !! a)
  ]
  where
    t'     = take kParam (Lam lam : t)
    sigma' = sigma ⊔! [varAddr ==> s (Clo (lam, rho))]

step ((Lit lit, _, SetK (x, varAddr, a), t), sigma) =
  [ ((Lit lit, Map.empty, kappa, t'), sigma')
  | Cont kappa <- Set.toList (sigma !! a)
  ]
  where
    t'     = take kParam (Lit lit : t)
    sigma' = sigma ⊔! [varAddr ==> s (LitVal lit)]


-- While cond body:
--   1. Evaluate cond
--   2. If true, evaluate body, then goto 1
--   3. If false, return #f (or unit)
--
-- Continuations:
--   WhileCondK: condition has been evaluated
--   WhileBodyK: body has been evaluated, loop back

-- (while cond body): evaluate condition first
step ((While cond body, rho, kappa, t), sigma) =
  [ ((cond, rho, WhileCondK (cond, body, rho, a'), t'), sigma') ]
  where
    t'     = take kParam (While cond body : t)
    a'     = allocKont (While cond body) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]

-- Condition evaluated: if truthy, evaluate body; if falsy, return #f
step ((Lam lam, rho, WhileCondK (cond, body, rho', a), t), sigma) =
  -- Lam is always truthy, so evaluate body
  [ ((body, rho', WhileBodyK (cond, body, rho', a), t'), sigma) ]
  where t' = take kParam (Lam lam : t)

step ((Lit lit, _, WhileCondK (cond, body, rho', a), t), sigma) =
  -- If condition is true: evaluate body and loop
  (if not (isFalsy (LitVal lit))
    then [ ((body, rho', WhileBodyK (cond, body, rho', a), t'), sigma) ]
    else []
  ) ++
  -- If condition is false: exit loop, return #f
  (if isFalsy (LitVal lit)
    then [ ((Lit (LBool False), Map.empty, kappa, t'), sigma)
         | Cont kappa <- Set.toList (sigma !! a)
         ]
    else []
  )
  where t' = take kParam (Lit lit : t)

-- Body evaluated: loop back, re-evaluate condition
step ((_, _, WhileBodyK (cond, body, rho', a), t), sigma) =
  [ ((cond, rho', WhileCondK (cond, body, rho', a), t'), sigma) ]
  where t' = take kParam (cond : t)

-- Primitives

-- (prim op e1 e2): evaluate e1, push PrimLeftK
step ((Prim op e1 e2, rho, kappa, t), sigma) =
  [ ((e1, rho, PrimLeftK (op, e2, rho, a'), t'), sigma') ]
  where
    t'     = take kParam (Prim op e1 e2 : t)
    a'     = allocKont (Prim op e1 e2) t'
    sigma' = sigma ⊔! [a' ==> s (Cont kappa)]

-- Left arg evaluated: now evaluate right arg
step ((Lit lit, _, PrimLeftK (op, e2, rho, a), t), sigma) =
  [ ((e2, rho, PrimRightK (op, LitVal lit, a), t'), sigma) ]
  where t' = take kParam (Lit lit : t)

-- Right arg evaluated: apply primop (handles concrete ints and AnyInt)
step ((Lit lit2, _, PrimRightK (op, LitVal lit1, a), t), sigma) =
  let t' = take kParam (Lit lit2 : t)
      results = applyPrimOp op lit1 lit2
  in [ ((Lit r, Map.empty, kappa, t'), sigma)
     | r <- results
     , Cont kappa <- Set.toList (sigma !! a)
     ]

step ((Lit _lit2, _, PrimRightK (_op, _, a), _t), _sigma) = []

-- Literal in operator position of Ar: not applicable, stuck
-- But literal returned to a continuation: depends on the continuation

step ((Lam _, _, Mt, _), _) = []
step ((Lit _, _, Mt, _), _) = []

-- Catch-all
step (st, _) = [] -- error $ "stuck state: " ++ show st

-- Primitive operation evaluation (abstract)
-- Returns a *list* of possible results: concrete ops yield one result,
-- but AnyInt yields multiple (both bools for comparisons, AnyInt for arithmetic).

applyPrimOp :: PrimOp -> Lit -> Lit -> [Lit]
-- Concrete × Concrete
applyPrimOp Add (LInt n1) (LInt n2) = [LInt (n1 + n2)]
applyPrimOp Sub (LInt n1) (LInt n2) = [LInt (n1 - n2)]
applyPrimOp Mul (LInt n1) (LInt n2) = [LInt (n1 * n2)]
applyPrimOp Eq  (LInt n1) (LInt n2) = [LBool (n1 == n2)]
applyPrimOp Lt  (LInt n1) (LInt n2) = [LBool (n1 < n2)]
applyPrimOp Gt  (LInt n1) (LInt n2) = [LBool (n1 > n2)]
-- Anything involving AnyInt: arithmetic yields AnyInt, comparisons yield both
applyPrimOp op _ _ | op `elem` [Add, Sub, Mul] = [AnyInt]
applyPrimOp op _ _ | op `elem` [Eq, Lt, Gt]    = [LBool True, LBool False]
applyPrimOp _ _ _ = []

-- Abstract Garbage Collection (Section 5)
--
-- LL(e, rho, sigma) computes live locations reachable from an expression
-- and its environment. Collecting garbage before each step improves
-- precision by allowing address reuse without spurious merging.
-- Live locations from an expression + environment

llExp :: Store -> Exp -> Env -> P Addr
llExp sigma e rho =
  let fvars = fv e
      addrs = Set.fromList [ rho ! x | x <- Set.toList fvars, x `Map.member` rho ]
  in reachable sigma addrs

-- Live locations from a continuation
llKont :: Store -> Kont -> P Addr
llKont _ Mt = Set.empty
llKont sigma (Ar (e, rho, a)) =
  Set.insert a (llExp sigma e rho) `Set.union` llStorable sigma a
llKont sigma (Fn (x :=> e, rho, a)) =
  Set.insert a (llExp sigma (Lam (x :=> e)) rho) `Set.union` llStorable sigma a
llKont sigma (IfK (e1, e2, rho, a)) =
  Set.insert a (llExp sigma e1 rho `Set.union` llExp sigma e2 rho) `Set.union` llStorable sigma a
llKont sigma (SetK (_, varAddr, a)) =
  Set.fromList [varAddr, a] `Set.union` llStorable sigma a
llKont sigma (WhileCondK (c, b, rho, a)) =
  Set.insert a (llExp sigma c rho `Set.union` llExp sigma b rho) `Set.union` llStorable sigma a
llKont sigma (WhileBodyK (c, b, rho, a)) =
  Set.insert a (llExp sigma c rho `Set.union` llExp sigma b rho) `Set.union` llStorable sigma a
llKont sigma (PrimLeftK (_, e, rho, a)) =
  Set.insert a (llExp sigma e rho) `Set.union` llStorable sigma a
llKont sigma (PrimRightK (_, val, a)) =
  Set.insert a (llStorableVal sigma val) `Set.union` llStorable sigma a

-- Live locations reachable from a store location
llStorable :: Store -> Addr -> P Addr
llStorable sigma a =
  Set.unions [ llStorableVal sigma sv | sv <- Set.toList (sigma !! a) ]

llStorableVal :: Store -> Storable -> P Addr
llStorableVal sigma (Clo (x :=> e, rho)) = llExp sigma (Lam (x :=> e)) rho
llStorableVal sigma (Cont k)             = llKont sigma k
llStorableVal _     (LitVal _)           = Set.empty

-- Transitive closure: find all reachable addresses from a root set
reachable :: Store -> P Addr -> P Addr
reachable sigma roots = go Set.empty (Set.toList roots)
  where
    go visited [] = visited
    go visited (a : rest)
      | a `Set.member` visited = go visited rest
      | otherwise =
          let newAddrs = llStorable sigma a
              unvisited = Set.toList (newAddrs `Set.difference` (Set.insert a visited))
          in go (Set.insert a visited) (unvisited ++ rest)

-- Garbage collect a store given roots from the current state
gc :: PartialState -> Store -> Store
gc (e, rho, kappa, t) sigma =
  let rootAddrs = llExp sigma e rho `Set.union` llKont sigma kappa
      live = reachable sigma rootAddrs
  in Map.restrictKeys sigma live

-- Store-widened fixpoint analysis (Section 2.5 / 7)
--
-- Instead of exploring (PartialState, Store) pairs with per-state stores,
-- we maintain a single global store shared across all partial states.
-- This reduces complexity from exponential to polynomial for k=0.
--
-- System = (P(PartialState), Store)
-- f(C, σ) = (C', σ'') where
--   Q' = { (c', σ') : c ∈ C and (c, σ) |-> (c', σ') }
--   C' = C ∪ { c' : (c', _) ∈ Q' }
--   σ'' = σ ⊔ ⊔{σ' : (_, σ') ∈ Q'}

-- Enable/disable abstract GC
useGC :: Bool
useGC = True

-- Maximum number of distinct integer values at one address before widening
intWideningThreshold :: Int
intWideningThreshold = 4

-- Widen a set of storables: if it contains more than N distinct integers,
-- collapse them all to AnyInt. This ensures the store is finite.
widenStorables :: P Storable -> P Storable
widenStorables vals =
  let ints = [ n | LitVal (LInt n) <- Set.toList vals ]
  in if length ints > intWideningThreshold
     then
       -- Remove all LInt values, add AnyInt
       let withoutInts = Set.filter (not . isConcreteInt) vals
       in Set.insert (LitVal AnyInt) withoutInts
     else vals
  where
    isConcreteInt (LitVal (LInt _)) = True
    isConcreteInt _                 = False

-- Widen the entire store
widenStore :: Store -> Store
widenStore = Map.map widenStorables

-- One iteration of the widened fixpoint
widen :: System -> System
widen (states, sigma) =
  let -- For each partial state, compute transitions using the global store
      -- (optionally with GC)
      transitions =
        [ (ps', sigma')
        | ps <- Set.toList states
        , let sigmaGC = if useGC then gc ps sigma else sigma
        , (ps', sigma') <- step (ps, sigmaGC)
        ]
      -- New partial states
      newStates = Set.fromList (map fst transitions)
      -- Join all output stores, then widen integers
      newStore = widenStore $ foldl (⊔) sigma (map snd transitions)
  in (states `Set.union` newStates, newStore)

-- Compute fixpoint
analyze :: Exp -> System
analyze e =
  let ps0 = toPartial (inject e)
      sigma0 = extractStore (inject e)
      sys0 = (Set.singleton ps0, sigma0)
  in fix widen sys0

-- Simple fixpoint iteration
fix :: Eq a => (a -> a) -> a -> a
fix f x =
  let x' = f x
  in if x' == x then x else fix f x'

-- Injection
inject :: Exp -> Sigma
inject e = (e, Map.empty, Map.empty, Mt, [])

toPartial :: Sigma -> PartialState
toPartial (e, rho, _, k, t) = (e, rho, k, t)

extractStore :: Sigma -> Store
extractStore (_, _, sigma, _, _) = sigma

-- Keep the old per-state exploration for comparison

aval :: Exp -> P Sigma
aval e = explore step' (inject e)
  where
    step' :: Sigma -> [Sigma]
    step' (e', rho, sigma, k, t) =
      [ (e'', rho', sigma', k', t')
      | ((e'', rho', k', t'), sigma') <- step ((e', rho, k, t), sigma)
      ]

explore :: (Ord a) => (a -> [a]) -> a -> P a
explore f s0 = search f Set.empty [s0]

search :: (Ord a) => (a -> [a]) -> P a -> [a] -> P a
search _ seen [] = seen
search f seen (hd : tl)
  | hd `Set.member` seen = search f seen tl
  | otherwise             = search f (Set.insert hd seen) (f hd ++ tl)

-- Analysis queries

isFinal :: PartialState -> Bool
isFinal (Lam _, _, Mt, _) = True
isFinal (Lit _, _, Mt, _) = True
isFinal _                 = False

finalStates :: System -> P PartialState
finalStates (states, _) = Set.filter isFinal states

finalValues :: System -> P Storable
finalValues sys = Set.fromList
  [ case ps of
      (Lam lam, rho, Mt, _) -> Clo (lam, rho)
      (Lit lit, _, Mt, _)   -> LitVal lit
      _ -> error "not final"
  | ps <- Set.toList (finalStates sys)
  ]

stateCount :: System -> Int
stateCount (states, _) = Set.size states

storeSize :: System -> Int
storeSize (_, sigma) = Map.size sigma

-- Pretty printing

showExp :: Exp -> String
showExp (Ref x)         = x
showExp (Lam (x :=> e)) = "(λ" ++ x ++ "." ++ showExp e ++ ")"
showExp (f :@ e)        = "(" ++ showExp f ++ " " ++ showExp e ++ ")"
showExp (If c t el)     = "(if " ++ showExp c ++ " " ++ showExp t ++ " " ++ showExp el ++ ")"
showExp (Set x e)       = "(set! " ++ x ++ " " ++ showExp e ++ ")"
showExp (While c b)     = "(while " ++ showExp c ++ " " ++ showExp b ++ ")"
showExp (Lit (LBool b)) = if b then "#t" else "#f"
showExp (Lit (LInt n))  = show n
showExp (Lit AnyInt)    = "Int⊤"
showExp (Prim op e1 e2) = "(" ++ showPrim op ++ " " ++ showExp e1 ++ " " ++ showExp e2 ++ ")"

showPrim :: PrimOp -> String
showPrim Add = "+"
showPrim Sub = "-"
showPrim Mul = "*"
showPrim Eq  = "="
showPrim Lt  = "<"
showPrim Gt  = ">"

showStorable :: Storable -> String
showStorable (Clo (x :=> e, _)) = "(λ" ++ x ++ "." ++ showExp e ++ ")"
showStorable (LitVal (LBool b)) = if b then "#t" else "#f"
showStorable (LitVal (LInt n))  = show n
showStorable (LitVal AnyInt)    = "Int⊤"
showStorable (Cont _)           = "<cont>"

showResults :: System -> String
showResults sys@(states, sigma) =
  let nStates = stateCount sys
      nStore  = storeSize sys
      fins    = finalStates sys
      nFin    = Set.size fins
      vals    = finalValues sys
  in unlines
    [ "Reachable states: " ++ show nStates
    , "Store locations:  " ++ show nStore
    , "Final states:     " ++ show nFin
    , "Result values:    " ++ show (Set.size vals)
    , "Values:"
    ] ++ unlines [ "  " ++ showStorable v | v <- Set.toList vals ]

-- Show what values a variable could hold (for inspecting loop invariants)
showVarValues :: System -> Var -> String
showVarValues (_, sigma) x =
  let addr = BAddr (x, [])  -- at k=0, addresses are (var, [])
      vals = sigma !! addr
      valStrs = [ showStorable v | v <- Set.toList vals, isValue v ]
  in x ++ " ∈ {" ++ intercalate ", " valStrs ++ "}"

-- Test programs

-- Identity: (λx.x)
ident :: Exp
ident = Lam ("x" :=> Ref "x")

-- Simple application: (λx.x)(λy.y)
test1 :: Exp
test1 = ident :@ Lam ("y" :=> Ref "y")

-- Two-argument: ((λf.f(λx.x))(λg.g(λy.y)))
test2 :: Exp
test2 = Lam ("f" :=> (Ref "f" :@ Lam ("x" :=> Ref "x")))
     :@ Lam ("g" :=> (Ref "g" :@ Lam ("y" :=> Ref "y")))

-- Conditional: (if #t (λx.x) (λy.y))
testIf :: Exp
testIf = If (Lit (LBool True)) (Lam ("x" :=> Ref "x")) (Lam ("y" :=> Ref "y"))

-- Conditional with false: (if #f 1 2)
testIfFalse :: Exp
testIfFalse = If (Lit (LBool False)) (Lit (LInt 1)) (Lit (LInt 2))

-- Primitive arithmetic: (+ 1 2)
testAdd :: Exp
testAdd = Prim Add (Lit (LInt 1)) (Lit (LInt 2))

-- Comparison: (< 1 2)
testLt :: Exp
testLt = Prim Lt (Lit (LInt 1)) (Lit (LInt 2))

-- Mutation: (let x = 1 in (set! x 2); x)
-- Encoded as: ((λx. ((λ_. x) (set! x 2))) 1)
testSet :: Exp
testSet = (Lam ("x" :=>
            ((Lam ("_" :=> Ref "x")) :@ (Set "x" (Lit (LInt 2))))))
       :@ (Lit (LInt 1))

-- While loop that counts down:
-- (let x = 3 in (while (> x 0) (set! x (- x 1))))
-- Encoded as: ((λx. (while (> x 0) (set! x (- x 1)))) 3)
testWhile :: Exp
testWhile = (Lam ("x" :=>
              While (Prim Gt (Ref "x") (Lit (LInt 0)))
                    (Set "x" (Prim Sub (Ref "x") (Lit (LInt 1))))))
         :@ (Lit (LInt 3))

-- Simple while: (while #f body) should terminate immediately
testWhileFalse :: Exp
testWhileFalse = While (Lit (LBool False)) (Lit (LInt 42))

-- Nested application with conditional:
-- ((λf. (if #t (f 1) (f 2))) (λx. (+ x 10)))
testCondApp :: Exp
testCondApp =
  (Lam ("f" :=> If (Lit (LBool True))
                   (Ref "f" :@ Lit (LInt 1))
                   (Ref "f" :@ Lit (LInt 2))))
  :@ (Lam ("x" :=> Prim Add (Ref "x") (Lit (LInt 10))))

-- Church numeral zero: (λf.λx.x)
zero :: Exp
zero = Lam ("f" :=> Lam ("x" :=> Ref "x"))

-- Church successor: (λn.λf.λx. f (n f x))
succE :: Exp
succE = Lam ("n" :=> Lam ("f" :=> Lam ("x" :=>
  (Ref "f" :@ (Ref "n" :@ Ref "f" :@ Ref "x")))))

-- succ zero
test3 :: Exp
test3 = succE :@ zero

-- Omega (non-terminating): (λx. x x)(λx. x x)
omega1 :: Exp
omega1 = Lam ("x" :=> (Ref "x" :@ Ref "x"))

omega :: Exp
omega = omega1 :@ omega1

main :: IO ()
main = do
  let tests =
        [ ("(λx.x)(λy.y)",           test1)
        , ("((λf.f(λx.x))(λg.g(λy.y)))", test2)
        , ("succ zero",               test3)
        , ("(if #t (λx.x) (λy.y))",  testIf)
        , ("(if #f 1 2)",            testIfFalse)
        , ("(+ 1 2)",                testAdd)
        , ("(< 1 2)",                testLt)
        , ("(set! x mutation)",      testSet)
        , ("(while #f body)",        testWhileFalse)
        , ("conditional application", testCondApp)
        ]

  mapM_ (\(name, prog) -> do
    putStrLn $ "=== " ++ name ++ " ==="
    putStrLn $ "  Program: " ++ showExp prog
    let result = analyze prog
    putStrLn $ showResults result
    ) tests

  -- While loop with variable inspection
  putStrLn "=== while loop (variable analysis) ==="
  putStrLn $ "  Program: " ++ showExp testWhile
  let whileResult = analyze testWhile
  putStrLn $ showResults whileResult
  putStrLn $ "  Loop invariant: " ++ showVarValues whileResult "x"
  putStrLn ""

  putStrLn "=== omega (non-terminating) ==="
  putStrLn $ "  Program: " ++ showExp omega
  let omegaResult = analyze omega
  putStrLn $ showResults omegaResult