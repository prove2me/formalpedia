-- Prove2me | solution 1 for lean_workbook_plus_4699
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:49.137811+00:00
-- url     : https://prove2.me/submissions/c7d7ff85-7759-4e0f-8dbe-5723be0353ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : a * x^2 + b * x + c = 0) :
  x^2 + b / a * x + c / a = 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - x), sq_nonneg (b - c), sq_nonneg (b - x), sq_nonneg (c - x), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + x), sq_nonneg (b + c), sq_nonneg (b + x), sq_nonneg (c + x)])
