-- Prove2me | solution 1 for lean_workbook_plus_47747
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:04.719917+00:00
-- url     : https://prove2.me/submissions/66a8e19c-6ff9-4194-ac2a-ef36c156d1fc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ≥ 6 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
