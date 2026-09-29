-- Prove2me | Definitions.Def_Bridges_GraphTheory_FiniteSizeSusceptibility
-- name    : Bridges_GraphTheory_FiniteSizeSusceptibility
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:30.928517+00:00
-- url     : https://prove2.me/theorems/e7543934-d02c-4685-9fdf-a043f4066e62
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_FiniteSizeSusceptibility
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.FiniteSizeSusceptibility`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/FiniteSizeSusceptibility.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Finite-Size Susceptibility for Fractional Transversals

This file introduces **finite-size susceptibility observables** for hypergraph
fractional transversal numbers, creating a rigorous bridge from LP sensitivity
of random combinatorial structures to finite-size scaling theory in the style
of statistical mechanics.

## Central definitions

* `edgeInsertionDelta` — the response of `τ*(H)` to inserting a single edge
* `susceptibilityMax` — the maximum insertion response over all admissible edges
* `susceptibilityAvg` — the mean insertion response
* `FiniteSizeSusceptibility` — structure bundling susceptibility observables
* `quadraticSusceptibility` — the sum of squared increments along an
  edge-exposure sequence, equal to the variance decomposition

## Main results

* `edgeInsertionDelta_nonneg` — insertion response is nonnegative (monotonicity)
* `edgeInsertionDelta_le_one` — insertion response is at most 1 (Lipschitz)
* `edgeInsertionDelta_abs_le_one` — absolute insertion response ≤ 1
* `susceptibilityMax_le_one` — max susceptibility bounded by 1
* `susceptibilityAvg_le_one` — mean susceptibility bounded by 1
* `exists_pseudocritical_index` — finite-size peak existence
* `variance_eq_quadSusceptibility` — variance decomposition identity
* `quadraticSusceptibility_le_length` — variance bounded by sequence length

## Application keywords

finite-size scaling, critical exponent, susceptibility, universality,
random hypergraphs, fractional transversal, linear programming phase transition,
martingale variance decomposition, fluctuation-dissipation principle,
pseudocritical density, optimization thermodynamics, combinatorial statistical mechanics
-/

open Finset BigOperators

/-! ## Hypergraph infrastructure (self-contained) -/

namespace OptCrit

/-- A hypergraph on vertex type `V` is a finite collection of edges. -/
structure Hypergraph (V : Type*) where
  edges : Finset (Finset V)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `x : V → ℝ` is a fractional transversal of `H` if it is nonnegative
    and the sum over each edge is at least 1. -/
def IsFracTransversal (H : Hypergraph V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ e ∈ H.edges, 1 ≤ ∑ v ∈ e, x v

/-- The value of a fractional transversal assignment. -/
noncomputable def fracTransversalValue (x : V → ℝ) : ℝ := ∑ v : V, x v

/-- The fractional transversal number: infimum of feasible values. -/
noncomputable def fracTransversalNum (H : Hypergraph V) : ℝ :=
  ⨅ (x : V → ℝ) (_ : IsFracTransversal H x), fracTransversalValue x

/-- Add an edge to a hypergraph. -/
def addEdge (H : Hypergraph V) (e : Finset V) : Hypergraph V :=
  ⟨insert e H.edges⟩


/-
Monotonicity: more edges ⟹ larger τ*.
-/


/-
τ*(H ∪ {e}) ≤ τ*(H) + 1, via LP perturbation.
-/

/-! ## Part I: Edge Insertion Response -/

/-- The **edge insertion delta**: Δτ*(H, e) := τ*(H ∪ {e}) - τ*(H). -/
noncomputable def edgeInsertionDelta (H : Hypergraph V) (e : Finset V) : ℝ :=
  fracTransversalNum (addEdge H e) - fracTransversalNum H





/-! ## Part II: Susceptibility Observables -/

/-- The set of all `d`-element subsets of V. -/
def allDEdges (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun e => e.card = d)



/-- **Maximum edge-insertion susceptibility**. -/
noncomputable def susceptibilityMax (H : Hypergraph V) (d : ℕ) : ℝ :=
  if h : (allDEdges V d).Nonempty then
    (allDEdges V d).sup' h (fun e => |edgeInsertionDelta H e|)
  else 0

/-- **Mean edge-insertion susceptibility**. -/
noncomputable def susceptibilityAvg (H : Hypergraph V) (d : ℕ) : ℝ :=
  if (allDEdges V d).card ≠ 0 then
    (∑ e ∈ allDEdges V d, |edgeInsertionDelta H e|) / (allDEdges V d).card
  else 0



/-! ## Part III: Susceptibility Bounds -/





/-
**Mean ≤ Max**: the average cannot exceed the maximum.
-/

/-! ## Part IV: Quadratic Susceptibility and Variance Decomposition -/

/-- The quadratic susceptibility: sum of squared increments.
    For an edge-exposure martingale, equals `Var(τ*(H_m))`. -/
noncomputable def quadraticSusceptibility (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (f (i + 1) - f i) ^ 2


/-
**Quadratic susceptibility ≤ n** when increments bounded by 1.
-/

/-
**Telescoping sum**: total displacement = f(n) - f(0).
-/

/-
**Variance = quadratic susceptibility** when cross-terms vanish
    (martingale orthogonality).
-/

/-! ## Part V: Pseudocritical Point Existence -/

/-
**Finite-size peak existence**: any function on {0,…,M} has a maximizer.
-/



/-! ## Part VI: Cross-Domain Cauchy-Schwarz Bridge -/

/-
**Cauchy-Schwarz for susceptibility**: squared total displacement ≤ n · χ².
-/

/-! ## Part VII: Finite-Size Scaling Conjecture -/


end OptCrit


