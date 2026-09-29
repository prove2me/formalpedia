-- Prove2me | solution 1 for lean_workbook_plus_46013
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:22.147458+00:00
-- url     : https://prove2.me/submissions/ea852b45-5ff1-48e4-954d-0aba28d74b3c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 3 / 2) : 1 / a + 1 / b - 1 / c ≤ 3 / (4 * a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
