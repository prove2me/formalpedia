-- Prove2me | solution 1 for lean_workbook_plus_30931
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:53.889708+00:00
-- url     : https://prove2.me/submissions/d8525ee1-a1c8-48b3-aeb0-44efd7a0f611

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx: x > 0) : x + 1/x ≥ 2 ∧ (x = 1 ↔ x + 1/x = 2) := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have key : x + 1/x - 2 = (x - 1)^2 / x := by
    field_simp
    ring
  have hnn : (x - 1)^2 / x ≥ 0 := div_nonneg (sq_nonneg _) hx.le
  refine ⟨by linarith, ?_, ?_⟩
  · intro h
    rw [h, one_div_one]
    norm_num
  · intro h
    have h2 : (x - 1)^2 / x = 0 := by linarith
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · have : x - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
      linarith
    · exact absurd h2 hx'
