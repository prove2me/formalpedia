-- Prove2me | solution 1 for lean_workbook_plus_6687
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:31.498386+00:00
-- url     : https://prove2.me/submissions/32b4a17b-59bc-487d-9553-1c62c38026c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a * b + b * c + c * a + 2 * a * b * c = 1) : 1 + 2 * (a + b + c) ≥ 32 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
