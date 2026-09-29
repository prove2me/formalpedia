-- Prove2me | solution 1 for lean_workbook_plus_65302
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:28.653431+00:00
-- url     : https://prove2.me/submissions/cf174050-a5ee-45ff-ac5b-2de26500fd40

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x * y + y * x + x = 1) : 2 * x * y + x = 1 := by
  (intros; linarith)
