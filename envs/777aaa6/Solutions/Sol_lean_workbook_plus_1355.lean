-- Prove2me | solution 1 for lean_workbook_plus_1355
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:10.609493+00:00
-- url     : https://prove2.me/submissions/fecb075e-ad4c-41f3-ad6f-1d8f223e0fc8

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y / (x * y + y + 1) + z / (y * z + z + 1) + x / (z * x + x + 1)) ≤ 1   := by
  have h1 : 0 < x * y + y + 1 := by positivity
  have h2 : 0 < y * z + z + 1 := by positivity
  have h3 : 0 < z * x + x + 1 := by positivity
  have hd : 0 < (x * y + y + 1) * (y * z + z + 1) * (z * x + x + 1) :=
    mul_pos (mul_pos h1 h2) h3
  apply (mul_le_mul_iff_right₀ hd).mp
  have he : (1 - (y / (x * y + y + 1) + z / (y * z + z + 1) + x / (z * x + x + 1))) *
      ((x * y + y + 1) * (y * z + z + 1) * (z * x + x + 1)) = (x * y * z - 1) ^ 2 := by
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
    ring
  nlinarith only [he, sq_nonneg (x * y * z - 1)]

#print axioms solution
