-- Prove2me | solution 1 for lean_workbook_plus_21682
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:49.067682+00:00
-- url     : https://prove2.me/submissions/264a6d20-f3fa-4d66-a80f-c70912f60871

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 ≤ 4 * (a * b + b * c + c * a) := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
