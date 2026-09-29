-- Prove2me | solution 1 for lean_workbook_plus_17853
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:51.344667+00:00
-- url     : https://prove2.me/submissions/a9c5f3d8-38cb-4448-b1a9-8703b00c8a0a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) (h : a^2 + b^2 + c^2 = 9) : 2 * (a + b + c) - a * b * c ≤ 10 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
