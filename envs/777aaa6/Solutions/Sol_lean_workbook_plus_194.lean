-- Prove2me | solution 1 for lean_workbook_plus_194
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:06.61349+00:00
-- url     : https://prove2.me/submissions/85d8f66d-5b3d-4e46-a481-d6e479ff93ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > 0) (h : x * (9 - x^2) = 10) : x^3 - 9 * x + 10 = 0 := by
  (intros; linarith)
