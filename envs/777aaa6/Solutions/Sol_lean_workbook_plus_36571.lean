-- Prove2me | solution 1 for lean_workbook_plus_36571
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:30.411601+00:00
-- url     : https://prove2.me/submissions/4bf2556f-09d2-4380-b0e3-75621de50888

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y + Real.sqrt (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) = 1) : x + y + Real.sqrt (2 * x ^ 2 + 2 * x * y + 3 * y ^ 2) = 1 := by
  (intros; simp_all)
