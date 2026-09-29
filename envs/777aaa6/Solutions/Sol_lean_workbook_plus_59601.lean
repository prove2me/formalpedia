-- Prove2me | solution 1 for lean_workbook_plus_59601
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:34:05.660094+00:00
-- url     : https://prove2.me/submissions/99de4d1e-e077-40b1-a4d6-ff28af8e4195

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b - 2) ^ 2 * ((a + b + 2) ^ 2 + 4) ≥ 0 := by
  (intros; positivity)
