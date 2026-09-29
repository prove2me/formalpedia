-- Prove2me | solution 1 for adjustment_bounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:18.862101+00:00
-- url     : https://prove2.me/submissions/8fa52f21-ac37-403b-a046-e75450de0a0a

-- Sol generated from Speculative/Logic/CausalPrediction.lean
import Mathlib
import Definitions.Def_Speculative_Logic_CausalPrediction

/-! # CatalogBuild.MachineLearning.Prediction.CausalPrediction

Auto-generated from theorem catalog database.
Domain: MachineLearning/Prediction
Declarations: 12
-/


noncomputable section


















































theorem solution(n : ℕ) (E_Y_XZ P_Z : Fin n → ℝ)
    (hP_nn : ∀ i, 0 ≤ P_Z i) (hP_sum : ∑ i, P_Z i = 1)
    (lo hi : ℝ) (h_bound : ∀ i, lo ≤ E_Y_XZ i ∧ E_Y_XZ i ≤ hi) :
    lo ≤ ∑ i, E_Y_XZ i * P_Z i ∧ ∑ i, E_Y_XZ i * P_Z i ≤ hi := by
  constructor
  · calc lo = lo * 1 := (mul_one _).symm
      _ = lo * ∑ i, P_Z i := by rw [hP_sum]
      _ = ∑ i, lo * P_Z i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, E_Y_XZ i * P_Z i := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (h_bound i).1 (hP_nn i)
  · calc ∑ i, E_Y_XZ i * P_Z i
        ≤ ∑ i, hi * P_Z i := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (h_bound i).2 (hP_nn i)
      _ = hi * ∑ i, P_Z i := by rw [Finset.mul_sum]
      _ = hi * 1 := by rw [hP_sum]
      _ = hi := mul_one _
