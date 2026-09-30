-- Prove2me | solution 1 for lean_workbook_plus_28998
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:12.359381+00:00
-- url     : https://prove2.me/submissions/648617a8-0e0b-423d-a0b9-c4c0aecefbd5

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z^2 / x^2 + (x^2 + y^2) / (2 * z^2)) ≥ 1 + y / x   := by
  have hd : 0 < 2 * x ^ 2 * z ^ 2 := by positivity
  have he : 2 * x ^ 2 * z ^ 2 *
      (z ^ 2 / x ^ 2 + (x ^ 2 + y ^ 2) / (2 * z ^ 2) - (1 + y / x)) =
      (x ^ 2 - z ^ 2) ^ 2 + (x * y - z ^ 2) ^ 2 := by
    field_simp [ne_of_gt hx, ne_of_gt hz]
    <;> ring
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [he, sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (x * y - z ^ 2)]

#print axioms solution
