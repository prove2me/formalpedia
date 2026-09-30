-- Prove2me | solution 1 for lean_workbook_plus_63976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:18.522352+00:00
-- url     : https://prove2.me/submissions/182d4eb5-3314-4d41-9052-4e8210d3934a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : (a + 1 / b) * (b + 1 / a) = 9 / 2) : a + b ≥ Real.sqrt 2 := by
  have hp : 0 < a * b := mul_pos ha hb
  have hi : (a + 1 / b) * (b + 1 / a) = (a * b + 1) ^ 2 / (a * b) := by
    field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
  rw [hi] at hab
  have hm := (div_eq_iff (ne_of_gt hp)).mp hab
  have he : (2 * a * b - 1) * (a * b - 2) = 0 := by nlinarith
  have hlo : (1 : ℝ) / 2 ≤ a * b := by
    rcases mul_eq_zero.mp he with h | h <;> linarith
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [sq_nonneg (a - b)]

#print axioms solution
