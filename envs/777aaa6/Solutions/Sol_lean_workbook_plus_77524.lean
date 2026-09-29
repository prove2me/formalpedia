-- Prove2me | solution 1 for lean_workbook_plus_77524
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:21.469068+00:00
-- url     : https://prove2.me/submissions/ab33da21-7c64-4bb2-9f78-c76a8b4b1392

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  (10 * x^2)^3 - 1^3 = (10 * x^2 - 1) * (100 * x^4 + 10 * x^2 + 1) := by
  (intros; linarith)
