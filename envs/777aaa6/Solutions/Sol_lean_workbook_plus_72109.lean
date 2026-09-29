-- Prove2me | solution 1 for lean_workbook_plus_72109
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:17.103712+00:00
-- url     : https://prove2.me/submissions/7e3432e2-f8bd-43b7-96e7-595fc15498db

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b x y : ℝ) : (x + (b - a * Real.sqrt 3) / 2) ^ 2 + (y + (a + b * Real.sqrt 3) / 2) ^ 2 ≥ 0 := by
  (intros; positivity)
