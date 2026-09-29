-- Prove2me | solution 1 for lean_workbook_plus_73589
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:05.063891+00:00
-- url     : https://prove2.me/submissions/14877f18-40e4-4f45-913c-4cca1b772807

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 5) (h₂ : a * b + b * c + c * a = 8) : a ^ 2 + b ^ 2 + c ^ 2 = 9 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
