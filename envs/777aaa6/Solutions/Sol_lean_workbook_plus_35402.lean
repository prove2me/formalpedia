-- Prove2me | solution 1 for lean_workbook_plus_35402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:15:05.710906+00:00
-- url     : https://prove2.me/submissions/708cf354-2d47-4707-ad0f-34d55316f441

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x z : ℝ) : (1 / (3 * x ^ 2) + 3 / z ^ 2) ≥ 2 / (x * z) := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_pow, mul_zero, zero_mul, div_zero, zero_add]
    positivity
  by_cases hz : z = 0
  · subst z
    simp only [zero_pow, mul_zero, zero_mul, div_zero, add_zero]
    positivity
  have hp : 0 < 3*x^2*z^2 := by positivity
  have hid : 2 / (x*z) = (6*x*z)/(3*x^2*z^2) := by field_simp; ring
  have hid2 : 1/(3*x^2)+3/z^2 = (z^2+9*x^2)/(3*x^2*z^2) := by field_simp; ring
  rw [hid, hid2]
  exact (div_le_div_iff_of_pos_right hp).mpr (by nlinarith [sq_nonneg (z-3*x)])
