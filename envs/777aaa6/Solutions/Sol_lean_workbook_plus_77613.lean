-- Prove2me | solution 1 for lean_workbook_plus_77613
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:34.613635+00:00
-- url     : https://prove2.me/submissions/94b4e62e-7c57-4ac8-8dca-3a480f3a06c6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : x > 9): (x+2)^3 < x^3 + 8*x^2 - 6*x +8 ∧ x^3 + 8*x^2 - 6*x +8 < (x+3)^3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
