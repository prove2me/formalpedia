-- Prove2me | solution 1 for RademacherWigner.expect_frac_large_eigenvalues_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:13:54.269064+00:00
-- url     : https://prove2.me/submissions/2674fa6d-0d53-4198-9a53-7f9954ed4cf8

import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_W_isHermitian
import Theorems.Thm_RademacherWigner_expect_normalizedMoment_two_mul_le
import Theorems.Thm_WignerBridge_frac_large_eigenvalues_le

set_option autoImplicit false
open scoped BigOperators
open RademacherWigner

theorem solution {N k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
    (ht : 0 < t) :
    RademacherWigner.expect (fun g : Config N =>
        (((Finset.univ.filter fun i =>
            t ≤ |(W_isHermitian g).eigenvalues i| / Real.sqrt (N : ℝ)).card : ℝ) / (N : ℝ)))
      ≤ ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by
  have hstep : RademacherWigner.expect (fun g : Config N =>
      (((Finset.univ.filter fun i =>
          t ≤ |(W_isHermitian g).eigenvalues i| / Real.sqrt (N : ℝ)).card : ℝ) / (N : ℝ)))
      ≤ RademacherWigner.expect (fun g : Config N =>
          WignerBridge.normalizedMoment (W g) (2 * k) / t ^ (2 * k)) := by
    unfold RademacherWigner.expect
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro g _
    exact WignerBridge.frac_large_eigenvalues_le hN (W_isHermitian g) k ht
  refine hstep.trans ?_
  have havg : RademacherWigner.expect (fun g : Config N =>
      WignerBridge.normalizedMoment (W g) (2 * k) / t ^ (2 * k)) =
      RademacherWigner.expect (fun g : Config N =>
        WignerBridge.normalizedMoment (W g) (2 * k)) / t ^ (2 * k) := by
    unfold RademacherWigner.expect
    rw [← Finset.sum_div]
    exact div_right_comm _ _ _
  rw [havg]
  exact div_le_div_of_nonneg_right
    (RademacherWigner.expect_normalizedMoment_two_mul_le (N := N) hk hN)
    (pow_nonneg ht.le _)
