-- Prove2me | solution 1 for lean_workbook_plus_25571
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:46.056788+00:00
-- url     : https://prove2.me/submissions/a9954a5e-6937-4a7f-8e0c-4dafaa7c28fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : 0 < b ∧ b ≤ a ∧ a ≤ 4 ∧ a + b ≤ 7) : a^2 + b^2 ≤ 25 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
