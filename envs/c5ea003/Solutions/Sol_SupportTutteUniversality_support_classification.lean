-- Prove2me | solution 1 for SupportTutteUniversality.support_classification
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:57:44.751949+00:00
-- url     : https://prove2.me/submissions/2105b0c0-4d04-4c89-9bef-9a6f3e90c66d

-- Sol generated from Bridges/old/SupportTutteUniversality.lean
import Mathlib
import Definitions.Def_Bridges_old_SupportTutteUniversality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Universal Support-Tutte Invariant: Full Universality and Cross-Domain Bridge

This file establishes the **universal factorization theorem** for
deletion–contraction invariants on M-convex supports, proves a cardinality
specialization, and provides a cross-domain bridge to matroid theory via
binary supports.

## Main Results

* `dc_invariant_factors_through_canonical` — Universal factorization (Theorem C)
* `dc_invariant_unique` — Uniqueness corollary (uses multi-step calc)
* `canonicalSupportEval_one_eq_card` — Cardinality specialization (Theorem B)
* `activity_partition` — Activity counting theorem
* `binary_support_card_recursion` — Bridge to matroid theory (Theorem D)

## References

* Murota, "Discrete Convex Analysis", SIAM, 2003
* Brylawski–Oxley, "The Tutte polynomial and its applications", 1992
-/

open Finset BigOperators Finsupp

attribute [local instance] Classical.propDecidable

open SupportTutteUniversality

variable {ι : Type*} [DecidableEq ι]

/-! ## Section 1: Core Definitions -/








/-! ## Section 2: Basic Lemmas -/








/-! ## Section 3: Measure Descent -/




/-! ## Section 4: Support Classification -/


/-! ## Section 5: Canonical Evaluation -/


/-! ## Section 6: Theorem A — Base Cases -/



/-! ## Section 7: Theorem C — Universal Factorization -/


/-! ## Section 8: Uniqueness Corollary -/


/-! ## Section 9: Partition and Cardinality -/




/-! ## Section 10: Theorem B — Cardinality Specialization -/

/-
**Theorem B (Cardinality specialization).**
    Evaluating at `xL = 1` recovers the support cardinality.
-/

/-! ## Section 11: Theorem D — Binary Support Bridge -/

/-
For binary supports, ordinary coordinates correspond exactly to
    having both 0-valued and 1-valued elements.
-/


/-
Binary support contraction produces binary support.
-/



/-! ## Section 12: Activity Counting -/






/-
**Activity partition theorem.** Coordinates partition into loops,
    ordinary, and trivial, so their counts sum to `|ground|`.
-/


open SupportTutteUniversality in
theorem solution(S : Finset (ι →₀ ℕ)) :
    S = ∅ ∨ S = {(0 : ι →₀ ℕ)} ∨
    (∃ i, IsOrdCoord S i) ∨ (∃ i, IsSLoop S i) := by
  by_cases hempty : S = ∅
  · exact Or.inl hempty
  · by_cases hall_zero : ∀ m ∈ S, m = 0
    · exact Or.inr (Or.inl (Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨Finset.nonempty_iff_ne_empty.mpr hempty, hall_zero⟩))
    · push_neg at hall_zero
      obtain ⟨m, hm, hm_ne⟩ := hall_zero
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm_ne
      by_cases hzero : ∃ m' ∈ S, m' i = 0
      · exact Or.inr (Or.inr (Or.inl ⟨i, hzero, m, hm, Nat.pos_of_ne_zero hi⟩))
      · push_neg at hzero
        exact Or.inr (Or.inr (Or.inr ⟨i, fun m' hm' =>
          Nat.pos_of_ne_zero (hzero m' hm')⟩))
