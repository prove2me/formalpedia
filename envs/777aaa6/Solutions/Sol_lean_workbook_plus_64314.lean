-- Prove2me | solution 1 for lean_workbook_plus_64314
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:56.511015+00:00
-- url     : https://prove2.me/submissions/6e68f120-afc3-4374-800a-267954822319

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 2 * (1 / (a * b) + 1 / (b * c) + 1 / (c * a)) ≤ (2 / 3) * (1 / a + 1 / b + 1 / c) ^ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
