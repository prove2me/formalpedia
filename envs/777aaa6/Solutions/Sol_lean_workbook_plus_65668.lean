-- Prove2me | solution 1 for lean_workbook_plus_65668
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:27.798988+00:00
-- url     : https://prove2.me/submissions/87b2922a-ce41-4050-8053-09e925cc7330

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : (a^4+b^4)+(b^4+c^4)+(c^4+a^4) ≥ (a*b*(a^2+b^2)+b*c*(b^2+c^2)+c*a*(c^2+a^2)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
