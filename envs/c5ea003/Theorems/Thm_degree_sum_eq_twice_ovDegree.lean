-- Prove2me | Theorems.Thm_degree_sum_eq_twice_ovDegree
-- name    : degree_sum_eq_twice_ovDegree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:30:23.565857+00:00
-- url     : https://prove2.me/theorems/572e74c8-7675-4387-8ecb-50040bc06c5b
-- title:
--   Degree sum eq twice ovDegree
-- statement:
--   Formal statement of `degree_sum_eq_twice_ovDegree` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem degree_sum_eq_twice_ovDegree{α : Type*} [DecidableEq α] {n : ℕ}
--       (F : Fin n → Finset α) :
--       ∑ i : Fin n, ovVertexDeg F i = 2 * OvDegree F := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalAlgebra/OverlapSpectrumTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalAlgebra/OverlapSpectrumTheory.lean#L202

-- Thm stub generated from Bridges/TropicalAlgebra/OverlapSpectrumTheory.lean
import Mathlib
import Definitions.Def_Bridges_TropicalAlgebra_OverlapSpectrumTheory
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Overlap Spectrum Theory: Partitions, Metrics, and Spectral Bridges

This file develops the **overlap spectrum** — the integer partition induced by
overlap class sizes — and establishes its invariance properties, metric
structure, and connections to spectral graph theory and coding theory.

## Mathematical Context

Given a family of n finsets (e.g., cycle supports of tropical kernel generators),
the overlap equivalence classes partition the index set {0, ..., n-1}. The sizes
of these classes form an integer partition of n, which we call the **overlap
spectrum**. This is a strictly finer invariant than the overlap class count.

## Main Definitions

* `OvEquiv` — overlap equivalence (reflexive-transitive closure of overlap)
* `ovSetoid` — the corresponding setoid on `Fin n`
* `ovClassCount` — number of overlap classes
* `overlapLaplacian` — the Laplacian matrix of the overlap graph
* `ovVertexDeg` — vertex degree in the overlap graph
* `ovComplexity` — sum of pairwise intersection sizes

## Main Results

* `ovClassCount_eq_of_pd` — class count = n when pairwise disjoint + nonempty
* `fully_connected_one_class'` — class count = 1 when every pair overlaps
* `class_count_le_universe` — n ≤ |α| for pairwise disjoint families
* `laplacian_trace_eq_degree_sum` — trace of Laplacian = sum of degrees
* `degree_sum_eq_twice_ovDegree` — handshaking lemma for overlap graph
* `laplacian_row_sum_zero` — Laplacian rows sum to zero
* `ovComplexity_zero_iff` — zero complexity ↔ pairwise disjoint
* `disjoint_implies_singleton_classes` — pairwise disjoint → each class is {i}
* `ovEquiv_exists_chain` — overlap equivalence implies existence of chain

## Cross-Domain Connections

* Tropical geometry → Partition theory (overlap spectrum)
* Graph theory → Spectral theory (overlap Laplacian)
* Combinatorics → Coding theory (support distance metric)
-/


open Finset BigOperators Classical

attribute [local instance] Classical.propDecidable

/-! ## Section 1: Support Overlap — Core Definitions -/











/-! ## Section 2: Pairwise Disjointness and Overlap Degree -/



/-! ## Section 3: Overlap Class Count -/



/-
**Key Theorem (by_contra + induction):**
    Class count = n when pairwise disjoint and nonempty.
-/

/-! ## Section 4: Fully Connected Regime -/

/-
**Deep Theorem (by_contra + rcases):**
    When every pair overlaps, there is exactly one overlap class.
-/

/-! ## Section 5: Overlap Laplacian — Cross-Domain Bridge to Spectral Theory -/




/-
**The Handshaking Lemma for the overlap graph (deep proof with Finset combinatorics):**
    Sum of vertex degrees = 2 × number of edges.
-/

theorem degree_sum_eq_twice_ovDegree{α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) :
    ∑ i : Fin n, ovVertexDeg F i = 2 * OvDegree F := by sorry
