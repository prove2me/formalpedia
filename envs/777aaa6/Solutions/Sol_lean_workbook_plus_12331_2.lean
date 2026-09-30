-- Prove2me | solution 2 for lean_workbook_plus_12331
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:29.021155+00:00
-- url     : https://prove2.me/submissions/e744e01a-d1d4-4d50-8ebd-2f53900c5ebd

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1 / (2 * x * y * z)) :  Real.sqrt (1 + x^4 + y^4 + z^4) ≥ x * y + y * z + z * x := by
  have hxyz : 0 < 2 * x * y * z := by positivity
  have h' : (x + y + z) * (2 * x * y * z) = 1 := by
    rw [h]; field_simp
  have key : (x * y + y * z + z * x) ^ 2 ≤ 1 + x^4 + y^4 + z^4 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2)]
  rw [ge_iff_le]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt key)
