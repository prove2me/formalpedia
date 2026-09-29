-- Prove2me | solution 1 for lean_workbook_plus_48935
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:26.005745+00:00
-- url     : https://prove2.me/submissions/1a2aab38-f46c-4f96-a187-fe39d4ed03fa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b * (a + b) = 1) (ha : a > 0) (hb : b > 0) : a / (a^3 + a + 1) = b / (b^3 + b + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
