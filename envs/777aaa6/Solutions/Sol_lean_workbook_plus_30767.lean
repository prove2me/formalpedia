-- Prove2me | solution 1 for lean_workbook_plus_30767
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:38.309386+00:00
-- url     : https://prove2.me/submissions/df07bd28-3e26-48fb-b110-abb9e58430b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 * x * y * z > 0 := by
  (intros; simp_all)
