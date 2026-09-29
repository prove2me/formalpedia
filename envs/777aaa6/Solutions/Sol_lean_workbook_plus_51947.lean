-- Prove2me | solution 1 for lean_workbook_plus_51947
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:29.543456+00:00
-- url     : https://prove2.me/submissions/f4443a4b-f17f-41bb-95d3-6ca21fbdc24d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 2 * b + 2 * c) + (c + a) / (b + 2 * c + 2 * a) + (a + b) / (c + 2 * a + 2 * b) ≤ 6 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
