-- Prove2me | solution 1 for Barrier4.netCost_ge_logb_sub_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:01:54.063258+00:00
-- url     : https://prove2.me/submissions/4592ad0f-ada1-4529-a9a0-7d947dd3f147

import Mathlib
import Definitions.Def_Tropical_Barrier4AdaptiveSaturation
open Barrier4 in
theorem solution {W : ℝ} (hW : 0 < W) (k : ℕ) :
    Real.logb 2 W - 1 / 2 ≤ netCost W k := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- the residual window `t = W / 2^k`
  set t := W / 2 ^ k with ht
  have htpos : 0 < t := div_pos hW h2k
  have hW' : W = t * 2 ^ k := by rw [ht]; field_simp
  have hlogW : Real.log W = Real.log t + k * Real.log 2 := by
    rw [hW', Real.log_mul htpos.ne' h2k.ne', Real.log_pow]
  have hnet : netCost W k = t / 2 + k := by
    unfold netCost
    rw [hW', pow_succ]
    field_simp
  have hlogb : Real.logb 2 W = Real.log t / Real.log 2 + k := by
    rw [Real.logb, hlogW]
    field_simp
  -- `ln t ≤ ln 2 · (t + 1) / 2`, from `ln x ≤ x - 1` at `x = t` or `x = t / 4`
  have key : Real.log t ≤ Real.log 2 * (t + 1) / 2 := by
    rcases le_total t 2 with h | h
    · have h1 := Real.log_le_sub_one_of_pos htpos
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo.le) (by linarith : (0 : ℝ) ≤ t + 1)]
    · have h4 : Real.log (t / 4) ≤ t / 4 - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h4' : Real.log (t / 4) = Real.log t - 2 * Real.log 2 := by
        rw [Real.log_div htpos.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.log_pow]
        push_cast
        ring
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo.le) (by linarith : (0 : ℝ) ≤ t - 2)]
  have hdiv : Real.log t / Real.log 2 ≤ (t + 1) / 2 := by
    rw [div_le_iff₀ hl2]
    linarith
  rw [hlogb, hnet]
  linarith
