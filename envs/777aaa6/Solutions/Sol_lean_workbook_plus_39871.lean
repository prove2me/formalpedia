-- Prove2me | solution 1 for lean_workbook_plus_39871
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:10.779904+00:00
-- url     : https://prove2.me/submissions/0bce3628-c3f3-4e4c-850f-33f5631c9600

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c ≤ 1) :
  (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤
    (3 + a + b + c) / (3 - (a + b + c)) * (b / a + c / b + a / c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
