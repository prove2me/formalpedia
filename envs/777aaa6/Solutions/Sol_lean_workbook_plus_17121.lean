-- Prove2me | solution 1 for lean_workbook_plus_17121
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:36.723281+00:00
-- url     : https://prove2.me/submissions/d2569571-8972-41e2-bbe1-fbe0c13909b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 1 / 2 * (a * b * c + 1) * (a + 1) * (b + 1) * (c + 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
