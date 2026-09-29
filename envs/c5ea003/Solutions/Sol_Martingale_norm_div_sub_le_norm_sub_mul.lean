-- Prove2me | solution 1 for Martingale.norm_div_sub_le_norm_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:17:25.796154+00:00
-- url     : https://prove2.me/submissions/3b6e7e6b-4f1f-49d2-8411-ea384712ecd0

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem solution (z u w : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖u / z - w‖ ≤ ‖u - z * w‖ := by
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hsplit : u / z - w = (u - z * w) / z := by field_simp
  rw [hsplit, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (u - z * w)]
