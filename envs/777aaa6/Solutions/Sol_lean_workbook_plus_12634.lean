-- Prove2me | solution 1 for lean_workbook_plus_12634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:51.173875+00:00
-- url     : https://prove2.me/submissions/ccc4f7bb-de26-4536-8bed-311f7f978694

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 1) : (a + b) / (3 + 5 * a * b) + (b + c) / (3 + 5 * b * c) + (c + a) / (3 + 5 * c * a) ≤ (3 * Real.sqrt 3) / 7 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
