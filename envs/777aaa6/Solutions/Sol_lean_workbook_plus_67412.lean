-- Prove2me | solution 1 for lean_workbook_plus_67412
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:35.07124+00:00
-- url     : https://prove2.me/submissions/3c55cd07-2b14-42da-8d92-44933ace6b01

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > -1) (hy : y > -1) (hxy : x + y = 1) : (x / (y + 1) + y / (x + 1)) ≥ 2 / 3   := by
  have hx1 : 0 < x + 1 := by linarith
  have hy1 : 0 < y + 1 := by linarith
  have hd : 0 < 3 * (x + 1) * (y + 1) := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp [ne_of_gt hx1, ne_of_gt hy1]
  nlinarith [sq_nonneg (x - y)]

#print axioms solution
