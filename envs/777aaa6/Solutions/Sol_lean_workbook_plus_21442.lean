-- Prove2me | solution 1 for lean_workbook_plus_21442
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:02.151742+00:00
-- url     : https://prove2.me/submissions/9b412889-73e9-42ee-9c9c-85996b2273a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
