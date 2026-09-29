-- Prove2me | solution 1 for lean_workbook_plus_76207
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:36.523431+00:00
-- url     : https://prove2.me/submissions/735c3170-8e01-4b5d-ac79-b0d650f64416

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A B : ℝ) : A + B = 0 ∧ A - B = 1/3 → A = 1/6 ∧ B = -1/6 := by
  (intros; constructor <;> nlinarith [sq_nonneg (A), sq_nonneg (B), sq_nonneg (A - B), sq_nonneg (A + B)])
