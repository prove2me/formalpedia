-- Prove2me | solution 1 for lean_workbook_plus_13937
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:36.69564+00:00
-- url     : https://prove2.me/submissions/5c0d3f1f-1e8b-4e2e-a6d0-126e214d2085

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (y - z) ^ 2 * (x - z) ^ 2 * (x - y) ^ 2 / (y ^ 2 * x ^ 2 * z ^ 2) ≥ 0 := by
  (intros; positivity)
