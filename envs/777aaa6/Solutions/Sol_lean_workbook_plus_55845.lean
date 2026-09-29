-- Prove2me | solution 1 for lean_workbook_plus_55845
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:21:57.081511+00:00
-- url     : https://prove2.me/submissions/a524b6eb-8ad0-4a81-9b30-9e31983c0a58

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a + b + c + 1 / (15 * a * b * c) ≥ 6 * Real.sqrt 3 / 5 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
