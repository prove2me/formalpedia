-- Prove2me | solution 1 for lean_workbook_plus_14644
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:58.49758+00:00
-- url     : https://prove2.me/submissions/47fe8515-ea51-4450-85cd-2ae3af36bc82

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 1) (h₂ : a^3 + b^3 + c^3 = 25) : (a - 1) * (b - 1) * (c - 1) = 8 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
