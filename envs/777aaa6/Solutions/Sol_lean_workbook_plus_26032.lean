-- Prove2me | solution 1 for lean_workbook_plus_26032
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:31.606367+00:00
-- url     : https://prove2.me/submissions/395b159e-a4c6-43f4-9ade-999913fdd7ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 2 * (x + y) = 14 → x + y = 7 := by
  (intros; linarith)
