-- Prove2me | solution 1 for lean_workbook_plus_65163
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:43.113278+00:00
-- url     : https://prove2.me/submissions/092da804-9840-4c5e-92f8-1db178cb0121

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (a b : ℝ) (ha : a = ⌊x^2⌋) (hb : b = x^2 - ⌊x^2⌋) : a + b = x^2 := by
  (intros; simp_all)
