-- Prove2me | solution 1 for lean_workbook_plus_33090
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:22.261329+00:00
-- url     : https://prove2.me/submissions/d3f90c71-2fa4-49f9-b159-0111a1a2318e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h₁ : (1 : ℝ)^4 + a * 1^3 + b * 1^2 + c * 1 + d = 10) (h₂ : (2 : ℝ)^4 + a * 2^3 + b * 2^2 + c * 2 + d = 20) (h₃ : (3 : ℝ)^4 + a * 3^3 + b * 3^2 + c * 3 + d = 30) : (12^4 + a * 12^3 + b * 12^2 + c * 12 + d + (-8)^4 + a * (-8)^3 + b * (-8)^2 + c * (-8) + d) / 10 = 1984 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
