-- Prove2me | solution 1 for interleaving_trans
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:16.816736+00:00
-- url     : https://prove2.me/submissions/bef29980-a5be-434d-9dfe-dabcefa755b8

-- Sol generated from Bridges/NeuralCoding/TropicalPersistenceStability.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_TropicalPersistenceStability
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Persistence Stability and Network Robustness

This file establishes the **tropical bottleneck stability theorem** for
weighted graph filtrations, together with computable robustness certificates
and cross-domain bridges to network science and metric geometry.

## Scientific Significance

The central claim is that **tropical Morse data on graphs is metrically
well-conditioned**: bounded perturbations of edge weights produce bounded
changes in the resulting tropical persistence data. This opens a program
of tropical topological statistics for noisy infrastructure networks,
biological interaction graphs, and learned weighted architectures.

## Main Definitions

* `TropicalGraphFiltration` — weighted graph with edge weights in ℝ
* `TropicalWeightPerturbation` — certified perturbation data
* `weightSupDist` — sup-norm distance on edge-weight functions
* `tropicalSublevelSet` — sublevel set of edges at threshold t
* `tropicalRankFunction` — rank function counting sublevel edges
* `tropicalInterleavedBy` — ε-interleaving of sublevel filtrations
* `mergeTime` — first threshold at which all edges are included
* `hasLongBar` — existence of a persistent topological feature
* `certifiedBarcodeShiftBound` — certified upper bound on barcode displacement

## Main Results

* `tropical_rank_interleaving_of_sup_bound` — sublevel set inclusion under perturbation
* `tropical_rank_interleaving_of_sup_bound_symm` — symmetric direction
* `tropical_rank_lipschitz` — 1-Lipschitz stability of interleaving
* `tropical_bottleneck_stability_rank` — bottleneck stability via rank functions
* `tropical_event_robust_of_margin` — certified robustness of topological events
* `long_bar_robust_under_weight_perturbation` — robust persistence of long bars
* `component_merge_time_lipschitz` — cross-domain: merge time is 1-Lipschitz
* `tropical_critical_value_lipschitz` — min/max weight observables are 1-Lipschitz
* `certifiedBarcodeShiftBound_correct` — verified algorithm correctness

## Application Keywords

topological data analysis, network robustness, uncertainty quantification,
interleavings, bottleneck distance, tropical geometry, noisy measurements,
certified inference, graph filtrations, phase transitions.

## References

* Cohen-Steiner, Edelsbrunner, Harer, "Stability of Persistence Diagrams" (2007)
* Baker, Norine, "Riemann–Roch and Abel–Jacobi theory on a finite graph" (2007)
* Mikhalkin, "Tropical geometry and its applications" (2006)
-/


open Finset BigOperators

noncomputable section

/-! ## Part 1: Core Definitions -/












/-! ## Part 2: Foundation Lemmas -/

/-- Membership in the sublevel set is equivalent to the weight being at most t. -/
theorem mem_tropicalSublevelSet {E : Type*} (w : E → ℝ) (t : ℝ) (e : E) :
    e ∈ tropicalSublevelSet w t ↔ w e ≤ t :=
  Iff.rfl






/-! ## Part 3: Theorem 1 — Sublevel Set Interleaving (core engine) -/






/-! ## Part 4: Theorem 2 — Rank Function Stability -/




/-! ## Part 5: Theorem 3 — Certified Robustness -/


/-
**Theorem 3b: Long bar robustness.**
    If weight range ≥ L + δ, perturbation < δ/2 preserves range ≥ L.
-/

/-! ## Part 6: Cross-Domain Theorems -/

/-
**Theorem 4a: Merge time is 1-Lipschitz.**
    The maximum edge weight cannot shift by more than the sup-norm perturbation.
-/

/-
**Theorem 4b: Minimum critical value is 1-Lipschitz.**
-/


/-
**Theorem 4d: Weight range is 2-Lipschitz.**
-/

/-! ## Part 7: Verified Algorithm -/


/-
**The certified bound is tight:** the interleaving is exact.
-/

/-
**Characterization of the optimal interleaving distance.**
-/

/-! ## Part 8: Structural Properties of Interleaving -/





theorem solution{E : Type*}
    (w₁ w₂ w₃ : E → ℝ) (ε₁ ε₂ : ℝ)
    (h₁₂ : tropicalInterleavedBy ε₁ w₁ w₂)
    (h₂₃ : tropicalInterleavedBy ε₂ w₂ w₃) :
    tropicalInterleavedBy (ε₁ + ε₂) w₁ w₃ := by
  constructor
  · intro t e he
    have h1 := h₁₂.1 t he
    have h2 := h₂₃.1 (t + ε₁) h1
    simp only [mem_tropicalSublevelSet] at h2 ⊢
    linarith
  · intro t e he
    have h1 := h₂₃.2 t he
    have h2 := h₁₂.2 (t + ε₂) h1
    simp only [mem_tropicalSublevelSet] at h2 ⊢
    linarith
