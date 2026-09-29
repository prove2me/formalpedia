-- Prove2me | solution 1 for lean_workbook_plus_69935
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:09.745805+00:00
-- url     : https://prove2.me/submissions/13c82dad-2ed3-4ee1-a90e-5d9f77137e60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : y * z * (y - z) ^ 2 * (2 * y ^ 2 + y * z + 2 * z ^ 2) ≥ 0 := by
  (intros; positivity)
