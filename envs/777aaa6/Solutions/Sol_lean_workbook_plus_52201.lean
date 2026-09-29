-- Prove2me | solution 1 for lean_workbook_plus_52201
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:57.627365+00:00
-- url     : https://prove2.me/submissions/364c8823-c278-4da2-ba2e-78bf99bb3770

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * (a + b) * (a + c) + b * (b + a) * (b + c) + c * (c + a) * (c + b) ≥ (4 / 9) * (a + b + c) ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
