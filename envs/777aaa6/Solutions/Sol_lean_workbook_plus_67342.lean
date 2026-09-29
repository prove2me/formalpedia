-- Prove2me | solution 1 for lean_workbook_plus_67342
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:16.845762+00:00
-- url     : https://prove2.me/submissions/d13d3edc-f9db-4fd7-9bd8-348e29ea3847

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  2 * (a^4 + b^4) ≥ (a^2 + b^2)^2 ∧ (a^2 + b^2)^2 ≥ 4 * a^2 * b^2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
