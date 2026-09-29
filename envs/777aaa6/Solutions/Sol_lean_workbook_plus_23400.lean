-- Prove2me | solution 1 for lean_workbook_plus_23400
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:05.810549+00:00
-- url     : https://prove2.me/submissions/d7a73b69-5402-46e3-b7a7-3614af4cea79

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a > b ∧ b > c) : (a - b + 1) ^ 2 ≥ 4 * (c - b) ∧ (c - a + 1) ^ 2 ≥ 4 * (b - a) := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
