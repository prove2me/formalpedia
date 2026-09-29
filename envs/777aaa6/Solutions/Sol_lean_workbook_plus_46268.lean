-- Prove2me | solution 1 for lean_workbook_plus_46268
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:11.083656+00:00
-- url     : https://prove2.me/submissions/29a9a086-a6a9-4198-a4a7-98fc963f91ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b * b + c * c) + b * (c * c + a * a) + c * (a * a + b * b) ≤ a * a * a + b * b * b + c * c * c + 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
