-- Prove2me | solution 1 for lean_workbook_plus_2328
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:11.722684+00:00
-- url     : https://prove2.me/submissions/d259ed22-0a11-4918-8abc-37327d67b1c6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c d e a : ℝ)
  (h₀ : b + c + d + e = 0)
  (h₁ : a + b + c + d + e = 1) :
  a^2 + b^2 + c^2 + d^2 + e^2 ≥ 1 / 4 := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (e), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (b + e), sq_nonneg (c + d), sq_nonneg (c + e), sq_nonneg (d + e)])
