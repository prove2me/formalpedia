-- Prove2me | solution 1 for lean_workbook_plus_2677
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:55.340724+00:00
-- url     : https://prove2.me/submissions/99a0f054-ee31-45fa-8f31-bb076808d1c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: x + 2*x > 6 - 3*x) : x > 1 := by
  (intros; linarith)
