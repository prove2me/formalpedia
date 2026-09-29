-- Prove2me | solution 1 for lean_workbook_plus_22085
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:29.922498+00:00
-- url     : https://prove2.me/submissions/c3174a7b-44cc-451c-80e6-1e6d7e855cb4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  (x^2 - 3 * x - 2)^2 - 3 * (x^2 - 3 * x - 2) - 2 - x = (x^2 - 4 * x - 2) * (x^2 - 2 * x - 4) := by
  (intros; linarith)
