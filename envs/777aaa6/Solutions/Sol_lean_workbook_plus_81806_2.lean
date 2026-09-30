-- Prove2me | solution 2 for lean_workbook_plus_81806
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:09.123309+00:00
-- url     : https://prove2.me/submissions/b2dbbe52-56d4-47da-8dad-9906c4b4095c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a ≥ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
