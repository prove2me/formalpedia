-- Prove2me | solution 1 for lean_workbook_plus_67665
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:39.269824+00:00
-- url     : https://prove2.me/submissions/a9ca3883-f2e8-43ac-a053-da32cb01b83c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ)
  (h₀ : a + b + c = 0) :
  a^2 + b^2 + c^2 = -2 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
