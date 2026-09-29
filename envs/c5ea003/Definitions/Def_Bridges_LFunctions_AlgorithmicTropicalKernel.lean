-- Prove2me | Definitions.Def_Bridges_LFunctions_AlgorithmicTropicalKernel
-- name    : Bridges_LFunctions_AlgorithmicTropicalKernel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:32.996613+00:00
-- url     : https://prove2.me/theorems/5b8effa9-26b3-4bca-8d5e-6c2f8781fad7
-- title:
--   Aether Catalog definitions — Bridges_LFunctions_AlgorithmicTropicalKernel
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LFunctions.AlgorithmicTropicalKernel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LFunctions/AlgorithmicTropicalKernel.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Algorithmic Tropical Kernel Computation for Weighted Graphs

This file develops a formal theory of algorithmic tropical kernel computation,
building on the weighted tropical Hodge infrastructure from `WeightedTropicalHodge.lean`.

The tropical kernel of a weighted graph — the set of vertex potentials satisfying a
local min-plus balance condition — is shown to be a **computable tropical convex
feasibility region** governed by local graph constraints. We prove translation
invariance, normalization reduction, neighbor domination bounds, and a bridge
to classical difference-constraint optimization.

## Mathematical Context

Classical graph Laplacians turn harmonicity into linear algebra. Tropical graph
Laplacians turn harmonicity into **min-plus balance geometry**. Once encoded as a
tropical inequality system, the kernel becomes accessible to optimization theory,
residuation methods, and network control.

## Main Definitions

* `IsInTropicalKernel` — global tropical balance at all vertices
* `IsNormalizedAt` — normalization fixing one vertex to zero
* `DifferenceConstraint` — classical difference constraint from tropical balance
* `normalize` — normalization preprocessor
* `inducedConstraint` — constraint extraction from minimizers

## Main Results

* `tropicalKernel_translation_invariant_iff` — translation invariance (iff)
* `tropicalKernel_feasible_iff_normalized` — feasibility = normalized feasibility
* `tropicalKernel_neighbor_domination` — each neighbor is dominated by another
* `tropicalKernel_minimizer_diff_bound` — minimizer yields difference constraints
* `tropicalKernel_implies_induced_system` — bridge to combinatorial optimization

## Application Keywords

tropical linear programming, min-plus algebra, graph Laplacian, weighted networks,
shortest paths, difference constraints, Bellman–Ford certificates, tropical Hodge theory,
sparse algorithms, combinatorial optimization, network resilience, routing,
power-grid equilibrium, discrete Hamilton–Jacobi, tropical convexity.

## References

* Baker–Norine (2007), "Riemann–Roch and Abel–Jacobi theory on a finite graph"
* Mikhalkin (2006), "Tropical geometry and its applications"
* Butkovič (2010), "Max-linear Systems: Theory and Algorithms"
-/


open Finset BigOperators Classical

noncomputable section

/-! ## Core Structure -/

/-- A weighted simple graph with integer edge weights. -/
structure WGraph (V : Type*) [Fintype V] where
  Adj : V → V → Prop
  adj_symm : Symmetric Adj
  loopless : ∀ v, ¬ Adj v v
  w : V → V → ℤ
  w_symm : ∀ ⦃u v⦄, Adj u v → w u v = w v u

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Fundamental Definitions -/

/-- The weighted neighbor value `w(i,j) + φ(j)` in the min-plus sense. -/
def wnv (G : WGraph V) (φ : V → ℤ) (i j : V) : ℤ :=
  G.w i j + φ j

/-- Tropical balance at vertex `i`: the minimum of `w(i,j) + φ(j)` over
    neighbors `j` is attained by at least two distinct neighbors. -/
def tropBalancedAt (G : WGraph V) (φ : V → ℤ) (i : V) : Prop :=
  ∃ j k : V, j ≠ k ∧ G.Adj i j ∧ G.Adj i k ∧
    G.wnv φ i j = G.wnv φ i k ∧
    ∀ l, G.Adj i l → G.wnv φ i j ≤ G.wnv φ i l

/-! ### New Definitions: Algorithmic Tropical Kernel -/

/-- **IsInTropicalKernel**: A vertex potential `φ` is in the tropical kernel of `G`
    if it satisfies the tropical balance condition at every vertex. -/
def IsInTropicalKernel (G : WGraph V) (φ : V → ℤ) : Prop :=
  ∀ v : V, G.tropBalancedAt φ v

/-- **IsInTropicalKernelOn**: Restriction of kernel membership to a vertex subset. -/
def IsInTropicalKernelOn (G : WGraph V) (S : Finset V) (φ : V → ℤ) : Prop :=
  ∀ v ∈ S, G.tropBalancedAt φ v

/-- **DifferenceConstraint**: A single constraint `φ(tgt) - φ(src) ≤ bound`. -/
structure DifferenceConstraint (V : Type*) where
  src : V
  tgt : V
  bound : ℤ

/-- A potential satisfies a single difference constraint. -/
def DifferenceConstraint.satisfied (c : DifferenceConstraint V) (φ : V → ℤ) : Prop :=
  φ c.tgt - φ c.src ≤ c.bound

/-- A potential satisfies a list of difference constraints. -/
def satisfiesAllConstraints (cs : List (DifferenceConstraint V)) (φ : V → ℤ) : Prop :=
  ∀ c ∈ cs, c.satisfied φ

/-! ### Theorem 1: Translation Invariance of the Tropical Kernel

The tropical kernel is invariant under adding a constant to all vertex potentials.
This is the tropical analogue of the classical Laplacian's constant-vector symmetry. -/




/-! ### Theorem 2: Feasibility Reduces to Normalized Feasibility

Fixing one vertex value to zero preserves solvability. -/



/-! ### Theorem 3: Neighbor Domination from Tropical Balance

At a balanced vertex, every neighbor is "dominated" by another distinct neighbor. -/



/-! ### Theorem 4: Minimizer Difference Constraints

From tropical balance, minimizing witnesses satisfy explicit difference constraints.
This is the bridge between tropical harmonicity and classical optimization. -/




/-! ### Theorem 5: Bridge to Difference Constraint Systems

We define a classical difference-constraint system induced by a tropical kernel
element and prove that every kernel element satisfies the induced constraints.
This connects tropical Hodge theory to mainstream combinatorial optimization. -/

/-- Construct the induced difference constraint from a minimizer `j` at vertex `u`
    against neighbor `v`: `φ(j) - φ(v) ≤ w(u,v) - w(u,j)`. -/
def inducedConstraint (G : WGraph V) (u j v : V) : DifferenceConstraint V :=
  { src := v, tgt := j, bound := G.w u v - G.w u j }



/-! ### Additional Structural Theorems -/





/-! ### Verified Computational Method: Normalization Preprocessor -/

/-- Normalize a potential at base vertex `v0`: subtract `φ(v0)` from all values. -/
def normalize (φ : V → ℤ) (v0 : V) : V → ℤ :=
  fun v => φ v - φ v0





/-! ### Verified Computational Method: Constraint Extraction -/

/-- Extract all induced constraints at vertex `u` with minimizer `j`,
    against a list of neighbors. -/
def extractConstraints (G : WGraph V) (u j : V) (neighbors : List V) :
    List (DifferenceConstraint V) :=
  neighbors.map (inducedConstraint G u j)


/-! ### Conjecture and Research Direction

**Conjecture (Sparse Normalized Tropical Feasibility):**
For every finite weighted graph `G` with maximum degree `Δ`, there exists a
polynomial-time algorithm deciding normalized tropical kernel feasibility
by reduction to a difference-constraint system with `O(|V| · Δ)` constraints.

The derived system is solvable by Bellman–Ford in `O(|V|² · Δ)` time.
On sparse graphs (Δ = O(1)), this gives `O(|V|²)` total time.

**Cross-domain connections:**
- **Combinatorial optimization:** Difference constraints, shortest paths, Bellman–Ford.
- **Tropical linear algebra:** Min-plus linear systems, residuation, tropical convexity.
- **Discrete Hamilton–Jacobi:** Tropically balanced potentials as viscosity solutions.
- **Chip-firing / divisor theory:** Kernel elements as balanced divisors (Baker–Norine). -/

end WGraph

end


