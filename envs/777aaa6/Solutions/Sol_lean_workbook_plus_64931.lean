-- Prove2me | solution 1 for lean_workbook_plus_64931
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:00.640619+00:00
-- url     : https://prove2.me/submissions/7c03bb6f-e39c-49b1-a57e-80af844f0813

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a ≥ 0 ∧ b ≥ 0 ∧ a^2 = b^2) : a = b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
