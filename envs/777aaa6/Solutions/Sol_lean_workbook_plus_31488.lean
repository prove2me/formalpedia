-- Prove2me | solution 1 for lean_workbook_plus_31488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:12.558765+00:00
-- url     : https://prove2.me/submissions/8af241f1-c011-46a4-9c8e-d8dd1d407497

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 3 * x^2 - 12 * x ≤ 0) :
  0 ≤ x ∧ x ≤ 4 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x)])
