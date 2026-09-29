-- Prove2me | solution 1 for lean_workbook_plus_22883
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:48.386156+00:00
-- url     : https://prove2.me/submissions/b26035dc-61e4-4c2a-9129-45e717a8f54d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a > 0 ∧ b > 0 ∧ c > 0 → 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
