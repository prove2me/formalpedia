-- Prove2me | solution 1 for lean_workbook_plus_29101
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:11.447754+00:00
-- url     : https://prove2.me/submissions/bb363010-4173-41cd-93b4-d982421fa59e

import Mathlib
set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a * b + b * c + c * a)) / (a + b) / (b + c) / (c + a) ≤ 9 / 4 / (a + b + c)   := by
  simp only [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_nonneg (le_of_lt ha) (sq_nonneg (b - c)),
    mul_nonneg (le_of_lt hb) (sq_nonneg (c - a)),
    mul_nonneg (le_of_lt hc) (sq_nonneg (a - b))]

#print axioms solution
