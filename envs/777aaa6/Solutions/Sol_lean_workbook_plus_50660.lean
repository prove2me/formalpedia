-- Prove2me | solution 1 for lean_workbook_plus_50660
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:01.248907+00:00
-- url     : https://prove2.me/submissions/2f8b1d12-055f-4305-8c03-cc63eaf3b7e5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a - b = 1) (h₂ : 2*a^2 + a*b - 3*b^2 = 22) : a = 5 ∧ b = 4 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
