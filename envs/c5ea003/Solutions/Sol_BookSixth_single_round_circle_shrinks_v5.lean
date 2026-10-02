-- Prove2me | solution 1 for BookSixth.single_round_circle_shrinks_v5
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:59:53.819682+00:00
-- url     : https://prove2.me/submissions/b9e11c71-e0cd-4035-bc2d-2213d4591c63

import Theorems.Thm_BookSixth_similarity_preserves_roundness
open BookSixth

set_option autoImplicit false

theorem solution (C : Set Space3) (hC : RoundCircle C) :
    ∃ K : {t : ℝ // 0 ≤ t ∧ t < 1} → Space3 ≃ₜ Space3,
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => K p.1 p.2) ∧
      (Continuous fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K ⟨0, le_rfl, zero_lt_one⟩ x = x) ∧
      (∀ t : {t : ℝ // 0 ≤ t ∧ t < 1}, RoundCircle ((K t) '' C)) := by
  let K (t : {t : ℝ // 0 ≤ t ∧ t < 1}) : Space3 ≃ₜ Space3 :=
    { toFun := fun x => (1 - t.1) • x
      invFun := fun x => (1 - t.1)⁻¹ • x
      left_inv := fun x => by
        simp [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt t.2.2))]
      right_inv := fun x => by
        simp [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt t.2.2))]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (1 - p.1.1) • p.2)
    fun_prop
  · change Continuous (fun p : {t : ℝ // 0 ≤ t ∧ t < 1} × Space3 => (1 - p.1.1)⁻¹ • p.2)
    apply Continuous.smul
    · apply Continuous.inv₀
      · fun_prop
      · intro p
        exact sub_ne_zero.mpr (ne_of_gt p.1.2.2)
    · exact continuous_snd
  · intro x
    simp [K]
  · intro t
    simpa only [K, add_zero] using
      similarity_preserves_roundness C (1 - t.1) 0 (sub_pos.mpr t.2.2) hC

