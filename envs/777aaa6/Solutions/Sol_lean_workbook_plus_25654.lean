-- Prove2me | solution 1 for lean_workbook_plus_25654
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:35.865986+00:00
-- url     : https://prove2.me/submissions/170e4b03-0ec4-4038-889f-8a58a2388407

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c q : ℝ) (h₁ : a ≤ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ q = (b + c - |a|) * (b + c + |a|)) : |a| ≥ b + c → q ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (q), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - q), sq_nonneg (b - c), sq_nonneg (b - q), sq_nonneg (c - q), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + q), sq_nonneg (b + c), sq_nonneg (b + q), sq_nonneg (c + q)])
