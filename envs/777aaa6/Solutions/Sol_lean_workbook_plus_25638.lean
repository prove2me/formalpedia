-- Prove2me | solution 1 for lean_workbook_plus_25638
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:44.941419+00:00
-- url     : https://prove2.me/submissions/1417654d-2c70-4e75-bf0e-dfe4d2ce2c53

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hxyz : x * y + y * z + z * x = 1) : x * z < 1 / 2   := by
  have hp : 0 ≤ (x - y) * (y - z) :=
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyz)
  by_cases hy0 : y = 0
  · have hx0 : 0 ≤ x := by simpa [hy0] using hxy
    have hz0 : z ≤ 0 := by simpa [hy0] using hyz
    have hn := mul_nonpos_of_nonneg_of_nonpos hx0 hz0
    linarith
  · nlinarith [sq_pos_of_ne_zero hy0]

#print axioms solution
