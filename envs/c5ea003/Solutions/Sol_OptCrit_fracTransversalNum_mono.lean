-- Prove2me | solution 1 for OptCrit.fracTransversalNum_mono
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:24:20.231536+00:00
-- url     : https://prove2.me/submissions/b666ba4b-5503-4e87-b2ea-df07599db979

-- Sol generated from Bridges/GraphTheory/FiniteSizeSusceptibility.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_FiniteSizeSusceptibility
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

open OptCrit


variable {V : Type*} [Fintype V] [DecidableEq V]





/-- Feasibility for a supergraph implies feasibility for a subgraph. -/
theorem IsFracTransversal_of_subset {H₁ H₂ : Hypergraph V}
    (h : H₁.edges ⊆ H₂.edges) (x : V → ℝ)
    (hx : IsFracTransversal H₂ x) : IsFracTransversal H₁ x :=
  ⟨hx.1, fun e he => hx.2 e (h he)⟩

/-
Monotonicity: more edges ⟹ larger τ*.
-/


/-
τ*(H ∪ {e}) ≤ τ*(H) + 1, via LP perturbation.
-/

/-! ## Part I: Edge Insertion Response -/






/-! ## Part II: Susceptibility Observables -/








/-! ## Part III: Susceptibility Bounds -/





/-
**Mean ≤ Max**: the average cannot exceed the maximum.
-/

/-! ## Part IV: Quadratic Susceptibility and Variance Decomposition -/



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



open OptCrit in
theorem solution{H₁ H₂ : Hypergraph V}
    (h : H₁.edges ⊆ H₂.edges) :
    fracTransversalNum H₁ ≤ fracTransversalNum H₂ := by
  refine' le_ciInf fun x => _;
  by_cases hx : IsFracTransversal H₂ x <;> simp +decide [ hx ];
  · refine' le_trans ( ciInf_le _ x ) _;
    · refine' ⟨ 0, Set.forall_mem_range.2 fun x => _ ⟩;
      refine' Real.iInf_nonneg fun _ => Finset.sum_nonneg fun _ _ => _;
      exact ‹IsFracTransversal H₁ x›.1 _;
    · exact ciInf_le ( by exact ⟨ 0, Set.forall_mem_range.2 fun _ => Finset.sum_nonneg fun _ _ => hx.1 _ ⟩ ) ( IsFracTransversal_of_subset h x hx );
  · refine' le_trans ( ciInf_le _ 0 ) _;
    · refine' ⟨ 0, Set.forall_mem_range.2 fun x => _ ⟩;
      refine' Real.iInf_nonneg _;
      exact fun hx => Finset.sum_nonneg fun _ _ => hx.1 _;
    · simp +decide [ fracTransversalValue ]
