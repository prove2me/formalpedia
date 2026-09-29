-- Prove2me | solution 1 for lean_workbook_plus_67029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:26.89612+00:00
-- url     : https://prove2.me/submissions/b6bc314f-60b9-4d08-b8c5-f6677d5168a3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a + b + c = 3) : -a - b - c = -3 := by
  (intros; linarith)
