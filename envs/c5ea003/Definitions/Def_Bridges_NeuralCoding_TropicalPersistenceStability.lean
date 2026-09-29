-- Prove2me | Definitions.Def_Bridges_NeuralCoding_TropicalPersistenceStability
-- name    : Bridges_NeuralCoding_TropicalPersistenceStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:40.104793+00:00
-- url     : https://prove2.me/theorems/b3189fa6-8609-4436-a4b3-ed52475dd9b5
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_TropicalPersistenceStability
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.TropicalPersistenceStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/TropicalPersistenceStability.lean by skeleton subtraction
import Mathlib
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



/-- The sup-norm distance between two edge-weight functions.
    This is the fundamental metric on the space of weighted filtrations. -/
def weightSupDist {E : Type*} [Fintype E] [Nonempty E] (w w' : E → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun e => |w e - w' e|)

/-- The sublevel set of edges at threshold t: edges whose weight is at most t.
    This is the basic building block of the tropical filtration. -/
def tropicalSublevelSet {E : Type*} (w : E → ℝ) (t : ℝ) : Set E :=
  {e | w e ≤ t}

/-- The tropical rank function: the number of edges in the sublevel set at
    threshold t. For finite edge sets, this is a step function that increases
    at each critical weight value. -/
def tropicalRankFunction {E : Type*} [Fintype E]
    (w : E → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun e => decide (w e ≤ t) = true)).card

/-- Two weight functions are ε-interleaved if their sublevel filtrations
    are mutually contained after ε-shifts. This is the tropical analogue
    of the classical persistence interleaving distance. -/
def tropicalInterleavedBy {E : Type*} (ε : ℝ) (w w' : E → ℝ) : Prop :=
  (∀ t : ℝ, tropicalSublevelSet w t ⊆ tropicalSublevelSet w' (t + ε)) ∧
  (∀ t : ℝ, tropicalSublevelSet w' t ⊆ tropicalSublevelSet w (t + ε))

/-- The merge time of a weight function: the maximum weight, i.e., the
    threshold at which all edges have entered the filtration. -/
def mergeTime {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun e => w e)

/-- The minimum critical value: the weight of the lightest edge. -/
def minCriticalValue {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty (fun e => w e)

/-- A long bar predicate: the range of weights spans at least L. -/
def hasLongBar {E : Type*} [Fintype E] [Nonempty E] (w : E → ℝ) (L : ℝ) : Prop :=
  mergeTime w - minCriticalValue w ≥ L

/-- Certified barcode shift bound: the sup-distance between weights gives
    an upper bound on barcode displacement. This is the verified algorithm. -/
def certifiedBarcodeShiftBound {E : Type*} [Fintype E] [Nonempty E]
    (w w' : E → ℝ) : ℝ :=
  weightSupDist w w'


/-! ## Part 2: Foundation Lemmas -/







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




end


