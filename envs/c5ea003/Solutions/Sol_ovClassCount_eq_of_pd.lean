-- Prove2me | solution 1 for ovClassCount_eq_of_pd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:20:47.528943+00:00
-- url     : https://prove2.me/submissions/e930f2e7-c714-4ce2-852a-37d43ef73cca

-- Sol generated from Bridges/TropicalAlgebra/OverlapSpectrumTheory.lean
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


/-- Class count ≤ n. -/
theorem ovClassCount_le {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α) :
    ovClassCount F ≤ n := by
  unfold ovClassCount
  calc Fintype.card (Quotient (ovSetoid F))
      ≤ Fintype.card (Fin n) := by
        have : Setoid (Fin n) := ovSetoid F
        exact Fintype.card_quotient_le (ovSetoid F)
    _ = n := Fintype.card_fin n

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

/-
**Laplacian row sums are zero (deep proof with field_simp-style reasoning).**
-/

/-! ## Section 6: Overlap Complexity -/


/-
**Overlap complexity zero ↔ pairwise disjoint (multi-step proof with rcases).**
-/

/-! ## Section 7: Universe Size Bound -/

/-
**In a pairwise disjoint family over a finite universe, n ≤ |α|.
    (Deep proof with calc chain.)**
-/

/-! ## Section 8: Overlap Chain Existence -/

/-
**If i and j are overlap-equivalent, there exists a finite chain
    connecting them (induction on ReflTransGen).**
-/

/-! ## Section 9: Singleton Classes from Disjointness -/


/-
**Pairwise disjoint + nonempty ⟹ singleton classes
    (deep proof with by_contra + induction).**
-/

/-! ## Section 10: TPE Invariance -/







/-! ## Section 11: Overlap Information Content -/


/-
Zero shared elements for disjoint families.
-/

/-! ## Section 12: Conjecture -/



/-! ## Section 13: Overlap Deficit -/




theorem solution{α : Type*} [DecidableEq α] {n : ℕ}
    (F : Fin n → Finset α)
    (hF : PDFamily F)
    (_hne : ∀ i, (F i).Nonempty) :
    ovClassCount F = n := by
  refine' le_antisymm ( ovClassCount_le _ ) _;
  convert Fintype.card_le_of_injective _ ( show Function.Injective ( Quotient.mk ( ovSetoid F ) ) from ?_ );
  · simp +decide;
  · intro i j hij;
    rw [ Quotient.eq ] at hij;
    -- By definition of `ovSetoid`, if `ovSetoid F i j`, then `i` and `j` are in the same overlap class.
    have h_overlap : ∀ i j, (ovSetoid F) i j → i = j := by
      intro i j hij; induction hij; aesop;
      rename_i k l hk hl ih; specialize hF k l; simp_all +decide [ SOverlap ] ;
      exact Classical.not_not.1 fun h => Finset.not_nonempty_iff_eq_empty.2 ( Finset.disjoint_iff_inter_eq_empty.1 ( hF h ) ) hl;
    grind
