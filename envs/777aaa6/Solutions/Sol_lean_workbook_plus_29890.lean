-- Prove2me | solution 1 for lean_workbook_plus_29890
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:53.244838+00:00
-- url     : https://prove2.me/submissions/66a7c195-5c47-40d0-b693-245dcb9eb4ab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : c ≥ b ∧ b ≥ a ∧ a ≥ 0) :
  (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
