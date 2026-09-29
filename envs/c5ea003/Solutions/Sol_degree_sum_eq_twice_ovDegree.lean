-- Prove2me | solution 1 for degree_sum_eq_twice_ovDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:32.529917+00:00
-- url     : https://prove2.me/submissions/a9aeb99b-87dd-49df-bdc9-3959fbd2124e

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
    (F : Fin n → Finset α) :
    ∑ i : Fin n, ovVertexDeg F i = 2 * OvDegree F := by
  convert Set.ncard_eq_toFinset_card' ( { p : Fin n × Fin n | p.1 ≠ p.2 ∧ SOverlap ( F p.1 ) ( F p.2 ) } ) using 1;
  · erw [ Set.ncard_eq_toFinset_card _ ] ; simp +decide [ ovVertexDeg ];
    simp +decide only [card_filter];
    erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_ite ];
    simp +decide only [eq_comm];
  · rw [ show ( { p : Fin n × Fin n | p.1 ≠ p.2 ∧ SOverlap ( F p.1 ) ( F p.2 ) }.toFinset : Finset _ ) = ( Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ SOverlap ( F p.1 ) ( F p.2 ) ) ∪ ( Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1 ∧ SOverlap ( F p.2 ) ( F p.1 ) ) from ?_, Finset.card_union_of_disjoint ];
    · rw [ show ( Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1 ∧ SOverlap ( F p.2 ) ( F p.1 ) ) = Finset.image ( fun p : Fin n × Fin n => ( p.2, p.1 ) ) ( Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ SOverlap ( F p.1 ) ( F p.2 ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; ring!;
      ext ⟨i, j⟩; simp [SOverlap];
    · exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => lt_asymm ( Finset.mem_filter.mp hp₁ |>.2.1 ) ( Finset.mem_filter.mp hp₂ |>.2.1 );
    · ext ⟨i, j⟩; simp [SOverlap];
      cases lt_trichotomy i j <;> simp +decide [ *, Finset.inter_comm ];
      · grind;
      · grind +splitImp
