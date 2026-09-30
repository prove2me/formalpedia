-- Prove2me | solution 2 for lean_workbook_plus_45111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:55.078497+00:00
-- url     : https://prove2.me/submissions/6181228b-2aac-4e95-be55-0e958471a08c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ 2 * ((b + c) / 2 - a)^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
