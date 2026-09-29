-- Prove2me | solution 1 for lean_workbook_plus_60177
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:05.84414+00:00
-- url     : https://prove2.me/submissions/84704fee-4848-4622-b359-bfab5ce250c9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
