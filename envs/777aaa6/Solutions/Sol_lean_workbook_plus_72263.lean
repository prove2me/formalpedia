-- Prove2me | solution 1 for lean_workbook_plus_72263
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:16.225558+00:00
-- url     : https://prove2.me/submissions/5e18f24e-1072-4064-87e9-0353e44fb36f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 6 * (x - 3.17)^2 + 11 * (y - 12.36)^2 ≥ 0 := by
  (intros; positivity)
