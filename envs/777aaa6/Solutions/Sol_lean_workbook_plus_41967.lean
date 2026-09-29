-- Prove2me | solution 1 for lean_workbook_plus_41967
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:42.951969+00:00
-- url     : https://prove2.me/submissions/d2192aed-ab80-40f5-b7d3-51e1e896599e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ^ 2 * (a - b) * (a - c) + b ^ 2 * (b - a) * (b - c) + c ^ 2 * (c - a) * (c - b) + (3 / 2) * ((a * b - c * a) ^ 2 + (b * c - a * b) ^ 2 + (c * a - b * c) ^ 2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
