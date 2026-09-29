-- Prove2me | solution 1 for lean_workbook_plus_52488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:27.855877+00:00
-- url     : https://prove2.me/submissions/6b43b142-9663-499e-9ea3-da05d2e40dd5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 2 * (-(Real.sqrt 6) + 2 * (Real.sqrt 3) - 3 * (Real.sqrt 2) + 2) = -2 * Real.sqrt 6 + 4 * Real.sqrt 3 - 6 * Real.sqrt 2 + 4 := by
  (intros; linarith)
