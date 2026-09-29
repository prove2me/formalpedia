-- Prove2me | solution 1 for WhichFactorWall.wall_imbalance_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T14:00:35.01852+00:00
-- url     : https://prove2.me/submissions/5dffcc24-bfdf-4b73-9a77-312724f93a8e

import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant

open WhichFactorWall Real Set in
theorem solution :
    ∃ p : ℝ, p ∈ Ioo (1/12 : ℝ) (1/9) ∧ binEntropy p = 0.4677 * log 2 ∧
      ∀ q ∈ Icc (0 : ℝ) 2⁻¹, binEntropy q = 0.4677 * log 2 → q = p := by
  -- rational enclosures of `log (2/3)` and `log (8/11)` from the log series
  have hA := Real.abs_log_sub_add_sum_range_le (x := 1 / 3) (by norm_num) 6
  have hB := Real.abs_log_sub_add_sum_range_le (x := 3 / 11) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hA hB
  obtain ⟨hA1, hA2⟩ := abs_le.1 hA
  obtain ⟨hB1, hB2⟩ := abs_le.1 hB
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  -- the two endpoint entropies in terms of `log 2`, `log (2/3)`, `log (8/11)`
  have e12 : Real.log 12 = 3 * Real.log 2 - Real.log (2 / 3) := by
    rw [show (12 : ℝ) = 2 ^ 3 / (2 / 3) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have e1211 : Real.log (12 / 11) = Real.log (8 / 11) - Real.log (2 / 3) := by
    rw [show (12 / 11 : ℝ) = (8 / 11) / (2 / 3) by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  have e9 : Real.log 9 = 2 * Real.log 2 - 2 * Real.log (2 / 3) := by
    rw [show (9 : ℝ) = 2 ^ 2 / (2 / 3) ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have e98 : Real.log (9 / 8) = -Real.log 2 - 2 * Real.log (2 / 3) := by
    rw [show (9 / 8 : ℝ) = (1 / 2) / (2 / 3) ^ 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring
  have hlo : binEntropy (1 / 12) < 0.4677 * Real.log 2 := by
    rw [binEntropy]
    norm_num
    rw [e12, e1211]
    nlinarith
  have hhi : 0.4677 * Real.log 2 < binEntropy (1 / 9) := by
    rw [binEntropy]
    norm_num
    rw [e9, e98]
    nlinarith
  -- existence by the intermediate value theorem
  obtain ⟨p, hp, hpv⟩ := intermediate_value_Ioo (show (1 / 12 : ℝ) ≤ 1 / 9 by norm_num)
    binEntropy_continuous.continuousOn ⟨hlo, hhi⟩
  refine ⟨p, hp, hpv, fun q hq hqv => ?_⟩
  -- uniqueness from strict monotonicity on `[0, 1/2]`
  have hpI : p ∈ Icc (0 : ℝ) 2⁻¹ := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  exact binEntropy_strictMonoOn.injOn hq hpI (hqv.trans hpv.symm)
