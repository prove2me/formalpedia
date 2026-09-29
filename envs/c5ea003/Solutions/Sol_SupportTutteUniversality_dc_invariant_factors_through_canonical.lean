-- Prove2me | solution 1 for SupportTutteUniversality.dc_invariant_factors_through_canonical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:59:27.574734+00:00
-- url     : https://prove2.me/submissions/4b07cb11-56ed-4702-9e46-6a40574fcffc

-- Sol generated from Bridges/old/SupportTutteUniversality.lean
import Mathlib
import Definitions.Def_Bridges_old_SupportTutteUniversality
import Theorems.Thm_SupportTutteUniversality_support_classification
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
theorem solution    {R : Type*} [CommSemiring R] (xL : R)
    (f : Finset (ι →₀ ℕ) → R)
    (hf_empty : f ∅ = 1)
    (hf_zero : f {(0 : ι →₀ ℕ)} = 1)
    (hf_ord : ∀ S i, IsOrdCoord S i →
      f S = f (sDelete S i) + f (sContract S i))
    (hf_loop : ∀ S i, IsSLoop S i → S.Nonempty →
      f S = xL * f (sContract S i))
    (S : Finset (ι →₀ ℕ)) :
    f S = canonicalSupportEval xL S := by
  induction' n : sMeasure S using Nat.strong_induction_on with n ih generalizing S
  unfold canonicalSupportEval
  split_ifs with h₁ h₂ h₃ h₄
  · rw [h₁, hf_empty]
  · rw [h₂, hf_zero]
  · rw [hf_ord S _ h₃.choose_spec]
    congr 1
    · exact ih _ (n ▸ sMeasure_delete_lt h₃.choose_spec.2) _ rfl
    · exact ih _ (n ▸ sMeasure_contract_lt_of_ordinary h₃.choose_spec) _ rfl
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h₁
    rw [hf_loop S _ h₄.choose_spec hne]
    congr 1
    exact ih _ (n ▸ sMeasure_contract_lt_of_loop h₄.choose_spec hne) _ rfl
  · have := support_classification S; tauto
