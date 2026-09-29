-- Prove2me | solution 1 for hammingWt_add_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:10:38.915916+00:00
-- url     : https://prove2.me/submissions/0551b7fd-6ad0-490f-b0d2-c822bb0dc6c7

-- Sol generated from Bridges/OperadicCodingTheory/HammingMetric.lean
import Mathlib
import Definitions.Def_Bridges_OperadicCodingTheory_HammingMetric

/-!
# Hamming Metric for Operadic Coding Theory

Bridge: connects **metric topology** to **information theory** (error-correcting codes).
Application: Hamming distance properties underpin certified robustness bounds for
post-quantum decoding pipelines and neural network verification.

## Main definitions
- `hammingWt`: Hamming weight of a vector (number of nonzero entries)
- `hammingDistFn`: Hamming distance between two vectors
- `LinearCodeParams`: Parameters [n, k, d] of a linear error-correcting code
- `LinearCodeParams.IsMDS`: Predicate characterizing maximum-distance-separable codes

## Main results
- `hammingDistFn_triangle`: Triangle inequality for Hamming distance
- `hammingDistFn_eq_zero`: Identity of indiscernibles
- `singleton_bound_from_params`: The Singleton bound d ≤ n − k + 1
- `mds_error_correction_optimal`: MDS codes have optimal error-correction radius
-/

noncomputable section

/-! ## Section 1: Hamming Weight -/








/-! ## Section 2: Hamming Distance -/









/-! ## Section 3: Code Parameters and Bounds -/













/-! ## Section 4: Hamming Ball Volume -/






/-! ## Section 5: Computational Examples -/








theorem solution{n : ℕ} {α : Type*} [DecidableEq α] [AddGroup α]
    (u v : Fin n → α) : hammingWt (u + v) ≤ hammingWt u + hammingWt v := by
  simp only [hammingWt]
  have hsub : Finset.univ.filter (fun i => (u + v) i ≠ 0) ⊆
      (Finset.univ.filter (fun i => u i ≠ 0)) ∪
        (Finset.univ.filter (fun i => v i ≠ 0)) := by
    intro i hi
    simp only [Pi.add_apply, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
               true_and] at hi ⊢
    by_contra h; push_neg at h
    exact hi (by simp [h.1, h.2])
  calc (Finset.univ.filter (fun i => (u + v) i ≠ 0)).card
      ≤ ((Finset.univ.filter (fun i => u i ≠ 0)) ∪
          (Finset.univ.filter (fun i => v i ≠ 0))).card :=
        Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
